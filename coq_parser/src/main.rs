use crate::interact::run_file;
use crate::project::read_project;

mod interact;
mod lexer;
mod parser;
mod project;

fn main() {
    let path = "/media/roman/36788FE1788F9E6D/NewProjects/Research/Coq/test/";
    let project = read_project(path).unwrap();

    let data = std::fs::read_to_string(&project.files[0]).unwrap();
    run_file(&project, &data).unwrap();
}
