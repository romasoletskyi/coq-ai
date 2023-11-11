use anyhow::{bail, Ok, Result};
use std::fs::{File, FileType};
use std::io::{BufRead, BufReader};
use std::{fmt, vec::Vec};
use walkdir::{WalkDir, DirEntry};

#[derive(Debug)]
struct ModuleArg {
    dir: String,
    coqdir: String,
}

impl fmt::Display for ModuleArg {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "-R {} {}", self.dir, self.coqdir)
    }
}

pub struct CoqProject {
    args: Vec<ModuleArg>,
    pub files: Vec<String>,
}

impl CoqProject {
    pub fn new() -> Self {
        CoqProject {
            args: Vec::new(),
            files: Vec::new(),
        }
    }
}

impl fmt::Display for CoqProject {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "ARGS")?;
        for arg in &self.args {
            writeln!(f, "{}", arg)?;
        }
        writeln!(f, "FILES")?;
        for file in &self.files {
            writeln!(f, "{}", file)?;
        }
        fmt::Result::Ok(())
    }
}

static PROJECT_FILE: &str = "_CoqProject";

fn parse_arg(line: &str, path: &str) -> Result<ModuleArg> {
    let words: Vec<&str> = line.split(' ').collect();
    if words.len() != 3 {
        bail!("parse_arg got -R with invalid number of arguments");
    }
    Ok(ModuleArg {
        dir: path.to_owned() + words[1],
        coqdir: words[2].to_owned(),
    })
}

fn read_project_file(path: &str, file: File) -> Result<CoqProject> {
    let mut project = CoqProject::new();
    let reader = BufReader::new(file);
    for line_result in reader.lines() {
        let line_check = line_result?;
        let line = line_check.trim();

        if line.starts_with("-R") {
            project.args.push(parse_arg(line, path)?);
        } else if !(line.starts_with('#') || line.starts_with('-') || line.is_empty()) {
            project.files.push(path.to_owned() + line);
        }
    }
    Ok(project)
}

fn read_simple_project(path: &str) -> Result<CoqProject> {
    let mut project = CoqProject::new();
    for entry in WalkDir::new(path) {
        let entry = entry?;
        let path = entry.path();
        if let Some(ext) = path.extension() {
            if ext.to_str().unwrap() == "v" {
                project.files.push(path.to_str().unwrap().to_string())
            }
        }
    }
    Ok(project)
}

pub fn read_project(path: &str) -> Result<CoqProject> {
    if let std::result::Result::Ok(file) = File::open(path.to_owned() + PROJECT_FILE) {
        read_project_file(path, file)
    } else {
        read_simple_project(path)
    }
}

pub(crate) fn prepare_program(project: &CoqProject) -> String {
    let mut program = "coqtop -color off".to_owned();
    for arg in &project.args {
        program.push_str(&format!(" {}", arg));
    }
    program
}
