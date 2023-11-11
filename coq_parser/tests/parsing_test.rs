use std::path::PathBuf;
use std::thread;

use coq_parser::{interact::run_file, project::{read_project, CoqProject}};

#[test]
fn test_file() {
    let project = CoqProject::new();
    let data = std::fs::read_to_string("tests/project/puzzles.v").unwrap();
    let mut writer = std::fs::File::create("data").unwrap();
    run_file(&project, &data, &mut writer).unwrap();
}

#[test]
fn parse_project() {
    let mut path = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    path.push("../dataset");

    let mut order = path.clone();
    order.push("repo-order");
    let repos: Vec<String> = std::fs::read_to_string(order).unwrap().split('\n').map(|s| s.to_string()).collect();  

    let thread_num = 32;
    let mut thread_repos = Vec::new();
    for _ in 0..thread_num {
        thread_repos.push(Vec::new());
    }    
    for i in 0..repos.len() {
        thread_repos[i % thread_num].push(repos[i].clone());
    }

    let mut handles = Vec::new();
    for i in 0..thread_num {
        handles.push(thread::spawn({
            let thread_repos = thread_repos[i].clone(); 
            let path = path.clone();
            move || {
            let mut writer = std::fs::File::create(format!("data-{}", i)).unwrap();
            for repo in thread_repos {
                let mut repo_path = path.clone();
                repo_path.push("github");
                repo_path.push(&repo);
        
                if let Ok(project) = read_project(&repo_path.display().to_string()) {
                    println!("Processing {}", repo_path.display());
                    for file in &project.files {
                        if let std::io::Result::Ok(data) = std::fs::read_to_string(file) {
                            let _ = run_file(&project, &data, &mut writer);
                        }
                    }
                }
            }
        }}));
    }

    for handle in handles {
        handle.join().unwrap();
    }
}
