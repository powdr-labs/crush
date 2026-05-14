// Build script that compiles the Lean implementation of
// `sequence_parallel_copies` and links it into the Rust crate.
//
//   1. Run `lake build` to translate `lean/ParallelCopies.lean` into
//      `lean/.lake/build/ir/ParallelCopies.c` (Lean's C backend output).
//   2. Compile that generated C plus our `lean/c/ffi.c` bridge into a static
//      archive via the `cc` crate.
//   3. Tell cargo to link the archive *and* `libleanshared`, which provides
//      the Lean runtime (heap allocator, GC, IO primitives, prelude inits).
//   4. Embed the toolchain's lib directory as an rpath so the dynamic loader
//      finds `libleanshared.so` at runtime without `LD_LIBRARY_PATH`.

use std::path::PathBuf;
use std::process::Command;

fn main() {
    let manifest_dir = PathBuf::from(env_var("CARGO_MANIFEST_DIR"));
    let lean_dir = manifest_dir.join("lean");

    // Locate the Lean toolchain.
    let lean_prefix = lean_print("--print-prefix");
    let lean_libdir = lean_print("--print-libdir");
    let lean_include = lean_prefix.join("include");

    // (1) Build the Lean library; this writes the generated C beside it.
    let lake_status = Command::new("lake")
        .arg("build")
        .current_dir(&lean_dir)
        .status()
        .expect("failed to spawn `lake build`");
    assert!(lake_status.success(), "lake build failed");

    let generated_c = lean_dir.join(".lake/build/ir/ParallelCopies.c");
    let ffi_c = lean_dir.join("c/ffi.c");

    // Rerun if any of the inputs change.
    println!("cargo:rerun-if-changed={}", lean_dir.join("ParallelCopies.lean").display());
    println!("cargo:rerun-if-changed={}", lean_dir.join("lakefile.toml").display());
    println!("cargo:rerun-if-changed={}", ffi_c.display());
    println!("cargo:rerun-if-changed=build.rs");

    // (2) Compile the C sources into a single static archive.
    cc::Build::new()
        .file(&generated_c)
        .file(&ffi_c)
        .include(&lean_include)
        // Lean's generated C uses some `static inline` helpers that gcc
        // warns about under -Wunused-function; silence to keep noise out.
        .flag_if_supported("-Wno-unused-function")
        .flag_if_supported("-Wno-unused-parameter")
        .flag_if_supported("-Wno-unused-but-set-variable")
        .flag_if_supported("-Wno-unused-variable")
        .compile("crush_lean_ffi");

    // (3) Link the Lean runtime statically. We deliberately avoid `libleanshared.so` because
    // it bundles its own libunwind, whose `_Unwind_RaiseException` then takes precedence over
    // the system libgcc_s version and breaks Rust's panic machinery. The static archives don't
    // export those symbols, so unwinding resolves to libgcc_s as it should.
    //
    // The flag order mirrors what `leanc --print-ldflags` emits, with the addition of
    // `cargo:rustc-link-search=native` so cargo can find each archive.
    let lean_tc_lib = lean_prefix.join("lib"); // libc++.a, libgmp.a, libuv.a live here
    println!("cargo:rustc-link-search=native={}", lean_libdir.display());
    println!("cargo:rustc-link-search=native={}", lean_tc_lib.display());

    // `--start-group ... --end-group` is needed because leancpp/Lean and Init/leanrt have
    // circular references between the archives.
    println!("cargo:rustc-link-arg=-Wl,--start-group");
    println!("cargo:rustc-link-arg=-lleancpp");
    println!("cargo:rustc-link-arg=-lLean");
    println!("cargo:rustc-link-arg=-Wl,--end-group");
    println!("cargo:rustc-link-arg=-lStd");
    println!("cargo:rustc-link-arg=-Wl,--start-group");
    println!("cargo:rustc-link-arg=-lInit");
    println!("cargo:rustc-link-arg=-lleanrt");
    println!("cargo:rustc-link-arg=-Wl,--end-group");
    println!("cargo:rustc-link-arg=-Wl,-Bstatic");
    println!("cargo:rustc-link-arg=-lc++");
    println!("cargo:rustc-link-arg=-lc++abi");
    println!("cargo:rustc-link-arg=-Wl,-Bdynamic");
    println!("cargo:rustc-link-arg=-Wl,--as-needed");
    println!("cargo:rustc-link-arg=-lgmp");
    println!("cargo:rustc-link-arg=-luv");
    println!("cargo:rustc-link-arg=-Wl,--no-as-needed");
    println!("cargo:rustc-link-arg=-lpthread");
    println!("cargo:rustc-link-arg=-ldl");
    println!("cargo:rustc-link-arg=-lrt");
    println!("cargo:rustc-link-arg=-lm");
    // libuv.a references `pthread_atfork`, which on modern glibc lives in libc.so. Rust's
    // default link line places `-lc` *before* our static archives, so re-link it here at the
    // end to satisfy the undef.
    println!("cargo:rustc-link-arg=-lc");
}

fn env_var(name: &str) -> String {
    std::env::var(name).unwrap_or_else(|_| panic!("missing env var {name}"))
}

fn lean_print(flag: &str) -> PathBuf {
    let output = Command::new("lean")
        .arg(flag)
        .output()
        .unwrap_or_else(|e| panic!("failed to run `lean {flag}`: {e}"));
    assert!(output.status.success(), "`lean {flag}` failed");
    let path = std::str::from_utf8(&output.stdout)
        .expect("non-utf8 path from lean")
        .trim();
    PathBuf::from(path)
}
