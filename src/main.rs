use std::fs::File;
use std::io::BufRead;

use crate::project::read_project;
use crate::interact::run_file;
use crate::lexer::Tokenizer;

mod project;
mod interact;
mod lexer;

fn main() {
    let path = "/media/roman/36788FE1788F9E6D/NewProjects/Research/Coq/topology/";
    let project = read_project(path).unwrap();
    //run_file(&project, &project.files[0]).unwrap();

    let data = std::fs::read_to_string(&project.files[0]).unwrap();    
    let mut tokenizer = Tokenizer::new(&data);
    let mut tokens = Vec::new();

    while let Some(token) = tokenizer.next().unwrap() {
        println!("{}", token);
        tokens.push(token);
    }
}