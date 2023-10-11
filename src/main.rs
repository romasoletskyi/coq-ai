use crate::project::read_project;
use crate::interact::run_file;

mod project;
mod interact;

fn main() {
    let path = "/media/roman/36788FE1788F9E6D/NewProjects/Research/Coq/test/";
    let project = read_project(path).unwrap();
    run_file(&project, &project.files[0]).unwrap();
}