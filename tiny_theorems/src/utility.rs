pub fn share<T>(vec: Vec<T>, thread_num: usize) -> Vec<Vec<T>> {
    let mut part_length = vec.len() / thread_num;
    if vec.len() - part_length * thread_num > 0 {
        part_length += 1;
    }
    let mut parts = vec![Vec::new()];
    for element in vec {
        if let Some(part) = parts.last() {
            if part.len() == part_length {
                parts.push(Vec::new());
            }
        }
        if let Some(part) = parts.last_mut() {
            part.push(element);
        }
    }
    while let Some(part) = parts.last() {
        if part.is_empty() {
            parts.pop().unwrap();
        } else {
            break;
        }
    }
    parts
}
