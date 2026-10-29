//! fx-driver: parse a document and run a query through the imported
//! `factoidal:subset/rdf` interface, `n` times each, and print the median
//! time of each call in microseconds as one JSON line.
//!
//! Usage: fx-driver <document> <format> <query.rq> [n]

wit_bindgen::generate!({ world: "driver", path: "wit", generate_all });

use factoidal::subset::rdf;
use std::time::Instant;

fn median(mut v: Vec<u128>) -> u128 {
    v.sort_unstable();
    v[v.len() / 2]
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    if args.len() < 4 {
        eprintln!("usage: fx-driver <document> <format> <query.rq> [n]");
        std::process::exit(2);
    }
    let doc = std::fs::read_to_string(&args[1]).expect("read document");
    let query = std::fs::read_to_string(&args[3]).expect("read query");
    let n: usize = args.get(4).map(|s| s.parse().expect("n")).unwrap_or(5);
    let mut parse_us = Vec::new();
    let mut query_us = Vec::new();
    let mut nq = String::new();
    let mut answer = String::new();
    for _ in 0..n {
        let t = Instant::now();
        nq = match rdf::parse(&doc, &args[2], "") {
            Ok(s) => s,
            Err(e) => {
                eprintln!("parse error: {e}");
                std::process::exit(1);
            }
        };
        parse_us.push(t.elapsed().as_micros());
        let t = Instant::now();
        answer = rdf::query(&nq, &query);
        query_us.push(t.elapsed().as_micros());
    }
    println!(
        "{{\"nquadsBytes\":{},\"parseUs\":{},\"queryUs\":{},\"answerBytes\":{},\"answerHead\":{:?}}}",
        nq.len(),
        median(parse_us),
        median(query_us),
        answer.len(),
        answer.chars().take(120).collect::<String>()
    );
}
