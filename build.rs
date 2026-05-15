// Build script that compiles the Lean implementation of
// `sequence_parallel_copies` and links it into the Rust crate.
//
//   1. Run `lake build` to translate `lean/ParallelCopies.lean` into
//      `lean/.lake/build/ir/ParallelCopies.c` (Lean's C backend output).
//   2. Compile that generated C plus our `lean/c/ffi.c` bridge into a static
//      archive via the `cc` crate.
//   3. Tell cargo to link the archive together with the official Lean static
//      archives (`libleancpp`, `libLean`, `libStd`, `libInit`, `libleanrt`)
//      plus `libc++`/`libc++abi`, GMP, and libuv — the recipe is the one
//      `leanc --print-ldflags` produces. We avoid `libleanshared.so` on
//      purpose: it bundles its own libunwind whose `_Unwind_RaiseException`
//      shadows libgcc_s's and breaks Rust's panic machinery.

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

    // Rerun if any Lean input changes. The proof and implementation live across
    // multiple files (ParallelCopies.lean, ParallelCopies/Spec.lean, Phase1.lean,
    // Phase2.lean, Proofs.lean, ...); without a directive for each of them Cargo
    // would skip the build script even after a real source change, leaving stale
    // generated C linked in.
    println!("cargo:rerun-if-changed={}", ffi_c.display());
    println!(
        "cargo:rerun-if-changed={}",
        lean_dir.join("lakefile.toml").display()
    );
    println!(
        "cargo:rerun-if-changed={}",
        lean_dir.join("lean-toolchain").display()
    );
    println!(
        "cargo:rerun-if-changed={}",
        lean_dir.join("lake-manifest.json").display()
    );
    for lean_file in collect_lean_sources(&lean_dir) {
        println!("cargo:rerun-if-changed={}", lean_file.display());
    }
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

/// Walk `lean_dir` and return every `*.lean` file underneath, excluding Lake's
/// build directory (`.lake/`). The result is used to emit `rerun-if-changed`
/// directives so Cargo notices edits to any Lean source.
fn collect_lean_sources(lean_dir: &std::path::Path) -> Vec<PathBuf> {
    fn walk(dir: &std::path::Path, out: &mut Vec<PathBuf>) {
        let entries = match std::fs::read_dir(dir) {
            Ok(e) => e,
            Err(_) => return,
        };
        for entry in entries.flatten() {
            let path = entry.path();
            let file_name = entry.file_name();
            // Skip Lake's build dir and any hidden dirs.
            if file_name == ".lake" || file_name.to_string_lossy().starts_with('.') {
                continue;
            }
            let file_type = match entry.file_type() {
                Ok(t) => t,
                Err(_) => continue,
            };
            if file_type.is_dir() {
                walk(&path, out);
            } else if path.extension().and_then(|s| s.to_str()) == Some("lean") {
                out.push(path);
            }
        }
    }
    let mut out = Vec::new();
    walk(lean_dir, &mut out);
    out
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
