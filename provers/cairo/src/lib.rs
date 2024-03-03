use lambdaworks_math::field::{
    element::FieldElement, fields::fft_friendly::stark_252_prime_field::Stark252PrimeField,
};

pub mod air;
pub mod cairo_layout;
pub mod cairo_mem;
pub mod decode;
pub mod errors;
pub mod execution_trace;
pub mod register_states;
pub mod runner;
pub mod transition_constraints;

#[cfg(test)]
pub mod tests;

#[cfg(feature = "wasm")]
pub mod wasm_wrappers;

pub type PrimeField = Stark252PrimeField;
pub type Felt252 = FieldElement<PrimeField>;

use crate::air::{generate_cairo_proof, verify_cairo_proof, PublicInputs};
use crate::cairo_layout::CairoLayout;
use crate::runner::run::generate_prover_args;
use stark_platinum_prover::proof::options::{ProofOptions, SecurityLevel};
use stark_platinum_prover::proof::stark::StarkProof;

use std::env;
use std::fs::File;
use std::io::{Error, ErrorKind};
use std::process::{Command, Stdio};

use std::mem;

#[repr(C)]
pub struct ByteData {
    data: *mut u8,
    len: usize,
}

#[repr(C)]
pub struct DoubleByteData {
    first: ByteData,
    second: ByteData,
}

#[no_mangle]
pub extern "C" fn free_byte_data(ptr: *mut ByteData) {
    if !ptr.is_null() {
        // This takes the pointer back into a Box, which will be dropped at the end of this scope
        let _b = unsafe { Box::from_raw(ptr) };
        // Dropping _b frees the ByteData and its contents
    }
}

#[no_mangle]
pub extern "C" fn free_double_byte_data(ptr: *mut DoubleByteData) {
    if !ptr.is_null() {
        // This takes the pointer back into a Box, which will be dropped at the end of this scope
        let _b = unsafe { Box::from_raw(ptr) };
        // Dropping _b frees the DoubleByteData and its contents
    }
}

/// Get current directory and return it as a String
fn get_root_dir() -> Result<String, Error> {
    let path_buf = env::current_dir()?.canonicalize()?;
    if let Some(path) = path_buf.to_str() {
        return Ok(path.to_string());
    }

    Err(Error::new(ErrorKind::NotFound, "not found"))
}

/// Attemps to compile the Cairo program with `cairo-compile`
/// and then save it to the desired path.  
/// Returns `Ok` on success else returns `Error`
fn cairo_compile(program_path: &String, out_file_path: &String) -> Result<(), Error> {
    let out_file = File::create(out_file_path)?;

    match Command::new("cairo-compile")
        .arg("--proof_mode")
        .arg(program_path)
        .stderr(Stdio::null())
        .stdout(out_file)
        .spawn()
    {
        Ok(mut child) => {
            // wait for spawned proccess to finish
            match child.wait() {
                Ok(_) => Ok(()),
                Err(err) => Err(err),
            }
        }
        Err(err) => Err(err),
    }
}

/// Attemps to compile the Cairo program with `docker`
/// and then save it to the desired path.  
/// Returns `Ok` on success else returns `Error`
fn docker_compile(program_path: &String, out_file_path: &String) -> Result<(), Error> {
    let out_file = File::create(out_file_path)?;
    let root_dir = get_root_dir()?;
    match Command::new("docker")
        .arg("run")
        .arg("--rm")
        .arg("-v")
        .arg(format!("{}/:/pwd", root_dir))
        .arg("cairo")
        .arg("--proof_mode")
        .arg(format!("/pwd/{}", program_path))
        .stderr(Stdio::null())
        .stdout(out_file)
        .spawn()
    {
        Ok(mut child) => {
            // wait for spawned proccess to finish
            match child.wait() {
                Ok(status) => match status.code() {
                    Some(0) => Ok(()), // exit success
                    _ => Err(Error::new(
                        ErrorKind::Other,
                        "File provided is not a Cairo uncompiled",
                    )),
                },
                Err(err) => Err(err),
            }
        }
        Err(err) => Err(err),
    }
}

/// Attemps to compile the Cairo program
/// with either `cairo-compile` or `docker``
fn try_compile(program_path: &String, out_file_path: &String) -> Result<(), Error> {
    if !program_path.contains(".cairo") {
        return Err(Error::new(
            ErrorKind::Other,
            "Provided file is not a Cairo source file",
        ));
    }

    if cairo_compile(program_path, out_file_path).is_ok()
        || docker_compile(program_path, out_file_path).is_ok()
    {
        Ok(())
    } else {
        Err(Error::new(
            ErrorKind::Other,
            "Failed to compile cairo program, neither cairo-compile nor docker found",
        ))
    }
}

#[no_mangle]
pub extern "C" fn generate_trace_and_inputs(
    program_content_bytes: *const u8,
    program_content_len: usize,
) -> *mut DoubleByteData {
    assert!(!program_content_bytes.is_null());
    let program_content =
        unsafe { std::slice::from_raw_parts(program_content_bytes, program_content_len) };

    // FIXME: We should set this through the CLI in the future
    let layout = CairoLayout::Plain;

    let Ok((main_trace, pub_inputs)) = generate_prover_args(&program_content, layout) else {
        eprintln!("Error generating prover args");
        return std::ptr::null_mut();
    };

    let main_trace_bytes: Vec<u8> =
        bincode::serde::encode_to_vec(&main_trace, bincode::config::standard())
            .expect("should be able to encode proof");
    let main_trace_data = main_trace_bytes.as_ptr() as *mut u8;
    let main_trace_len = main_trace_bytes.len();
    mem::forget(main_trace_bytes); // Prevent rust from freeing this memory as we pass it to python.

    let pub_inputs_bytes: Vec<u8> =
        bincode::serde::encode_to_vec(&pub_inputs, bincode::config::standard())
            .expect("should be able to encode pub inputs");
    let pub_inputs_data = pub_inputs_bytes.as_ptr() as *mut u8;
    let pub_inputs_len = pub_inputs_bytes.len();
    mem::forget(pub_inputs_bytes);

    let double_byte_data = DoubleByteData {
        first: ByteData {
            data: main_trace_data,
            len: main_trace_len,
        },
        second: ByteData {
            data: pub_inputs_data,
            len: pub_inputs_len,
        },
    };

    Box::into_raw(Box::new(double_byte_data))
}

// returns stark proof and public inputs with shared memory
#[no_mangle]
pub extern "C" fn generate_proof_from_trace(
    main_trace_bytes: *const u8,
    main_trace_len: usize,
    pub_inputs_bytes: *const u8,
    pub_inputs_len: usize,
) -> *mut ByteData {
    assert!(!main_trace_bytes.is_null());
    assert!(!pub_inputs_bytes.is_null());

    let main_trace_bytes = unsafe { std::slice::from_raw_parts(main_trace_bytes, main_trace_len) };
    let pub_inputs_bytes = unsafe { std::slice::from_raw_parts(pub_inputs_bytes, pub_inputs_len) };

    let (main_trace, _) =
        bincode::serde::decode_from_slice(main_trace_bytes, bincode::config::standard())
            .expect("should be able to decode trace table");
    let (pub_inputs, _) =
        bincode::serde::decode_from_slice(pub_inputs_bytes, bincode::config::standard())
            .expect("should be able to decode public inputs");

    // ## Prove
    let proof_options = ProofOptions::new_secure(SecurityLevel::Provable100Bits, 3);
    println!("Making proof ...");
    let proof = match generate_cairo_proof(&main_trace, &pub_inputs, &proof_options) {
        Ok(p) => p,
        Err(err) => {
            eprintln!("Error generating proof: {:?}", err);
            return std::ptr::null_mut();
        }
    };

    let proof_bytes: Vec<u8> = bincode::serde::encode_to_vec(&proof, bincode::config::standard())
        .expect("should be able to encode proof");
    let proof_data = proof_bytes.as_ptr() as *mut u8;
    let proof_len = proof_bytes.len();
    mem::forget(proof_bytes); // Prevent rust from freeing this memory as we pass it to python.

    let byte_data = ByteData {
        data: proof_data,
        len: proof_len,
    };

    Box::into_raw(Box::new(byte_data))
}

#[no_mangle]
pub extern "C" fn verify_proof(
    proof_bytes: *const u8,
    proof_len: usize,
    pub_inputs_bytes: *const u8,
    pub_inputs_len: usize,
) -> bool {
    let proof_bytes = unsafe { std::slice::from_raw_parts(proof_bytes, proof_len) };
    let pub_inputs_bytes = unsafe { std::slice::from_raw_parts(pub_inputs_bytes, pub_inputs_len) };

    let (proof, _) = bincode::serde::decode_from_slice(proof_bytes, bincode::config::standard())
        .expect("should be able to decode proof");
    let (pub_inputs, _) =
        bincode::serde::decode_from_slice(pub_inputs_bytes, bincode::config::standard())
            .expect("should be able to decode pub inputs");
    // Generate options
    let proof_options = ProofOptions::new_secure(SecurityLevel::Provable100Bits, 3);

    println!("Verifying ...");
    let proof_verified = verify_cairo_proof(&proof, &pub_inputs, &proof_options);

    if proof_verified {
        println!("Verification succeeded");
    } else {
        println!("Verification failed");
    }

    proof_verified
}

fn write_proof(
    proof: StarkProof<Stark252PrimeField, Stark252PrimeField>,
    pub_inputs: PublicInputs,
    proof_path: String,
) {
    let mut bytes = vec![];
    let proof_bytes: Vec<u8> =
        bincode::serde::encode_to_vec(proof, bincode::config::standard()).unwrap();

    let pub_inputs_bytes: Vec<u8> =
        bincode::serde::encode_to_vec(&pub_inputs, bincode::config::standard()).unwrap();

    // This should be reworked
    // Public inputs shouldn't be stored in the proof if the verifier wants to check them

    // An u32 is enough for storing proofs up to 32 GiB
    // They shouldn't exceed the order of kbs
    // Reading an usize leads to problem in WASM (32 bit vs 64 bit architecture)

    bytes.extend((proof_bytes.len() as u32).to_le_bytes());
    bytes.extend(proof_bytes);
    bytes.extend(pub_inputs_bytes);

    let Ok(()) = std::fs::write(&proof_path, bytes) else {
        eprintln!("Error writing proof to file: {}", &proof_path);
        return;
    };

    println!("Proof written to {}", &proof_path);
}

fn main() {
    println!("no!");
}
