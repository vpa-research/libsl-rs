use std::fs;

use insta::{assert_ron_snapshot, Settings};
use libsl::{LibSl, WithLibSl};
use pathdiff::diff_paths;

#[test]
fn test_snapshots() {
    let mut settings = Settings::clone_current();
    settings.set_omit_expression(true);
    let _guard = settings.bind_to_scope();

    insta::glob!("test-data/**/*.libsl", |path| {
        let contents = fs::read_to_string(path)
            .map_err(|e| format!("could not read `{}` to string: {e}", path.display()))
            .unwrap();

        let mut settings = Settings::clone_current();
        settings.set_description(format!("// Input file:\n{contents}"));
        let _guard = settings.bind_to_scope();

        let mut libsl = LibSl::new();
        let ast = libsl.parse_file(
            diff_paths(path, env!("CARGO_MANIFEST_DIR")).unwrap().display().to_string(),
            &contents
        );

        assert_ron_snapshot!(match &ast {
            Ok(file) => Ok(file.with_libsl(&libsl)),
            Err(e) => Err(e.to_string()),
        });
    });
}
