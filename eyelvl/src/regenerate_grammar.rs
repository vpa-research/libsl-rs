use std::ffi::OsStr;
use std::fmt::Write;
use std::path::{Path, PathBuf};
use std::process::{Command, ExitCode};
use std::{env, fs, io};

use color_eyre::eyre::{Context, Result, bail, eyre};

pub fn regenerate_grammar(
    grammar_dir: PathBuf,
    output_dir: PathBuf,
    antlr_path: PathBuf,
) -> Result<ExitCode> {
    eprintln!("Generating a parser from the ANTLR grammar files...");

    match fs::create_dir_all(&output_dir) {
        Ok(_) => {}

        Err(e) if e.kind() == io::ErrorKind::AlreadyExists => {}

        Err(e) => {
            return Err(eyre!(
                "could not create the output directory `{}`",
                output_dir.display()
            )
            .wrap_err(e));
        }
    }

    let _ = grammar_dir;
    let output_dir = output_dir
        .canonicalize()
        .wrap_err_with(|| format!("could not canonicalize `{}`", output_dir.display()))?;
    let antlr_path = antlr_path
        .canonicalize()
        .wrap_err_with(|| format!("could not canonicalize `{}`", antlr_path.display()))?;

    env::set_current_dir(&grammar_dir).wrap_err_with(|| {
        format!(
            "could not change the current directory to `{}",
            grammar_dir.display(),
        )
    })?;

    let grammar_files = find_files_with_ext(".", "g4")?;

    if grammar_files.is_empty() {
        bail!(
            "no grammar files found in {} (did you init the submodule?)",
            grammar_dir.display(),
        );
    }

    let mut cmd = Command::new("java");
    cmd.arg("-jar")
        .arg(&antlr_path)
        .arg("-Dlanguage=Rust")
        .arg("-o")
        .arg(&output_dir)
        .arg("-lib")
        .arg("./")
        .arg("-lib")
        .arg(&output_dir)
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
        .wrap_err("could not run the ANTLR tool")?
        .wait()
        .wrap_err("could not retrieve the exit status of the ANTLR tool")?;

    if !status.success() {
        bail!("encountered a failure running the ANTLR tool: {status}");
    }

    eprintln!("The ANTLR tool finished successfully with {status}");

    rename_generated_files(&output_dir)?;
    generate_grammar_mod_rs(&output_dir)?;

    Ok(ExitCode::SUCCESS)
}

static NAME_MAP: &[(&str, &str)] = &[
    ("libsllexer.rs", "lexer.rs"),
    ("libslparser.rs", "parser.rs"),
    ("libslparserlistener.rs", "parser_listener.rs"),
];

fn rename_generated_files(path: impl AsRef<Path>) -> Result<()> {
    let path = path.as_ref();

    for entry in
        fs::read_dir(path).wrap_err_with(|| format!("could not list `{}`", path.display()))?
    {
        let entry = entry.wrap_err_with(|| {
            format!("failed to read a directory entry of `{}`", path.display(),)
        })?;

        let Some((_, rename_to)) = NAME_MAP
            .iter()
            .copied()
            .find(|&(k, _)| k == entry.file_name().to_string_lossy().as_ref())
        else {
            continue;
        };

        let src = entry.path();
        let dst = src.with_file_name(rename_to);
        fs::rename(&src, &dst).wrap_err_with(|| {
            format!(
                "could not rename `{}` to `{}`",
                src.display(),
                dst.display(),
            )
        })?;
    }

    Ok(())
}

fn generate_grammar_mod_rs(path: impl AsRef<Path>) -> Result<()> {
    let path = path.as_ref();
    let mod_rs_path = path.join("mod.rs");
    eprintln!("Generating `{}`...", mod_rs_path.display());

    let rs_files = find_files_with_ext(path, "rs").wrap_err("could not list generated sources")?;
    let mut mod_rs = String::new();

    for path in rs_files {
        if path.file_name().unwrap().eq_ignore_ascii_case("mod.rs") {
            continue;
        }

        if !mod_rs.is_empty() {
            let _ = writeln!(mod_rs);
        }

        let name = path.file_stem().unwrap().to_string_lossy();

        let _ = writeln!(mod_rs, "#[allow(unused_parens)]");
        let _ = writeln!(mod_rs, "#[allow(clippy::all)]");
        let _ = writeln!(mod_rs, "pub mod {name};");

        if let Some((orig, _)) = NAME_MAP
            .iter()
            .copied()
            .find(|(_, v)| *v == path.file_name().unwrap().to_string_lossy())
        {
            let orig_name = orig.strip_suffix(".rs").unwrap();
            let _ = writeln!(mod_rs, "#[allow(unused_imports)]");
            let _ = writeln!(mod_rs, "use {name} as {orig_name};");
        }
    }

    fs::write(&mod_rs_path, mod_rs)
        .wrap_err_with(|| format!("could not write to `{}`", mod_rs_path.display()))?;

    Ok(())
}

fn find_files_with_ext(path: impl AsRef<Path>, ext: impl AsRef<OsStr>) -> Result<Vec<PathBuf>> {
    let path = path.as_ref();
    let ext = ext.as_ref();

    fs::read_dir(path)
        .wrap_err_with(|| format!("could not list `{}`", path.display()))?
        .map(|r| {
            r.map(|entry| entry.path()).wrap_err_with(|| {
                format!("failed to read a directory entry of `{}`", path.display())
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
