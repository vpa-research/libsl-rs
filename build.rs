use std::fmt::Write;
use std::ffi::OsStr;
use std::path::{Path, PathBuf};
use std::process::{Command, ExitCode};
use std::sync::LazyLock;
use std::{env, fs, io};

type Result<T = (), E = String> = std::result::Result<T, E>;

static GRAMMAR_DIR: LazyLock<PathBuf> = LazyLock::new(|| PathBuf::from("grammar/"));
const ANTLR_PATH_ENV: &str = "ANTLR_PATH";

fn main() -> ExitCode {
    println!("cargo::rerun-if-changed=build.rs");

    if let Err(e) = generate_grammar() {
        eprintln!("Encountered a failure: {e}");

        return ExitCode::FAILURE;
    }

    ExitCode::SUCCESS
}

fn generate_grammar() -> Result {
    eprintln!("Generating a parser from the ANTLR grammar files...");

    println!("cargo::rerun-if-changed={}", GRAMMAR_DIR.display());

    println!("cargo::rerun-if-env-changed={ANTLR_PATH_ENV}");
    let antlr_path = PathBuf::from(env::var_os(ANTLR_PATH_ENV).ok_or_else(|| {
        format!("environment variable `{ANTLR_PATH_ENV}` must be set before building the crate")
    })?);
    println!("cargo::rerun-if-changed={}", antlr_path.display());

    let grammar_files = find_files_with_ext(&*GRAMMAR_DIR, "g4")?;

    if grammar_files.is_empty() {
        return Err("no grammar files found (did you init the submodule?)".to_string());
    }

    let out_dir = PathBuf::from(env::var_os("OUT_DIR").unwrap());
    let gen_grammar_dir = out_dir.join(&*GRAMMAR_DIR);
    fs::create_dir_all(&gen_grammar_dir).map_err(|e| {
        format!(
            "could not create the output directory `{}`: {e}",
            gen_grammar_dir.display()
        )
    })?;

    let mut cmd = Command::new("java");
    cmd.arg("-jar")
        .arg(&antlr_path)
        .arg("-Dlanguage=Rust")
        .arg("-o")
        .arg(&out_dir)
        .arg("-lib")
        .arg(&*GRAMMAR_DIR)
        .arg("-lib")
        .arg(out_dir.join(&*GRAMMAR_DIR))
        .args(grammar_files)
        .stdout(io::stderr());

    eprintln!(
        "Running `{} {}`...",
        cmd.get_program().to_string_lossy(),
        cmd.get_args().fold(String::new(), |mut acc, arg| {
            if !acc.is_empty() {
                acc.push(' ');
            }

            acc.push_str(&arg.to_string_lossy());

            acc
        }),
    );

    let status = cmd
        .spawn()
        .map_err(|e| format!("could not run the ANTLR tool: {e}"))?
        .wait()
        .map_err(|e| format!("could not retrieve the exit status of the ANTLR tool: {e}"))?;

    if !status.success() {
        return Err(format!(
            "encountered a failure running the ANTLR tool: {status}"
        ));
    }

    eprintln!("The ANTLR tool finished successfully with {status}");

    generate_grammar_mod_rs(&gen_grammar_dir)?;

    Ok(())
}

fn generate_grammar_mod_rs(path: impl AsRef<Path>) -> Result {
    let path = path.as_ref();
    let mod_rs_path = path.join("mod.rs");
    eprintln!("Generating `{}`...", mod_rs_path.display());

    let rs_files = find_files_with_ext(path, "rs")
        .map_err(|e| format!("could not list generated sources: {e}"))?;
    let mut mod_rs = String::new();

    for path in rs_files {
        if path.file_name().unwrap().eq_ignore_ascii_case("mod.rs") {
            continue;
        }

        if !mod_rs.is_empty() {
            let _ = writeln!(mod_rs);
        }

        let _ = writeln!(mod_rs, "#[allow(unused_parens)]");
        let _ = writeln!(mod_rs, "pub mod {};", path.file_stem().unwrap().to_string_lossy());
    }

    fs::write(&mod_rs_path, mod_rs)
        .map_err(|e| format!("could not write to `{}`: {e}", mod_rs_path.display()))?;

    Ok(())
}

fn find_files_with_ext(path: impl AsRef<Path>, ext: impl AsRef<OsStr>) -> Result<Vec<PathBuf>> {
    let path = path.as_ref();
    let ext = ext.as_ref();

    fs::read_dir(path)
        .map_err(|e| format!("could not list `{}`: {e}", path.display()))?
        .map(|r| {
            r.map(|entry| entry.path()).map_err(|e| {
                format!(
                    "failed to read a directory entry of `{}`: {e}",
                    path.display(),
                )
            })
        })
        .filter(|res| match res {
            Ok(path) => path
                .extension()
                .is_some_and(|e| e.eq_ignore_ascii_case(ext)),
            Err(_) => true,
        })
        .collect()
}
