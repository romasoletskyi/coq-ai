use std::path::PathBuf;

use coq_parser::{interact::run_file, project::read_project};

#[test]
fn parse_project() {
    let mut path = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    path.push("tests/project/");
    let project = read_project(&path.display().to_string()).unwrap();

    let data = std::fs::read_to_string(&project.files[0]).unwrap();
    run_file(&project, &data).unwrap();
}
