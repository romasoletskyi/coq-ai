use crate::project::read_project;
use crate::interact::run_file;
use crate::lexer::CoqTokenizer;

mod project;
mod interact;
mod lexer;

fn main() {
    let path = "/media/roman/36788FE1788F9E6D/NewProjects/Research/Coq/test/";
    let project = read_project(path).unwrap();

    let data = std::fs::read_to_string(&project.files[0]).unwrap();    
    let mut tokenizer = CoqTokenizer::new(&data);
    let mut tokens = Vec::new();

    while let Some(token) = tokenizer.next().unwrap() {
        println!("{}", token);
        tokens.push(token);
    }

    run_file(&project, tokens.as_slice().into()).unwrap();
}