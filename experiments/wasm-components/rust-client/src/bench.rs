//! The driver shared by wc-client (component import) and wc-static (direct
//! call into the statically linked Lean objects). `E` is the engine: two
//! functions with the WIT signatures.
use std::time::Instant;

pub trait Engine {
    fn turtle_to_nquads(&self, ttl: &str) -> Result<String, String>;
    fn query(&self, ttl: &str, rq: &str) -> String;
}

const SAMPLE_TTL: &str = "@prefix ex: <http://example.org/> .\nex:a ex:p ex:b , ex:c .\n";
const SAMPLE_RQ: &str = "SELECT ?o WHERE { ?s ?p ?o } ORDER BY ?o";

/// `[]`: run the sample. `[--small N]`: N queries over the sample, the mean
/// time per call (the cost of the boundary on a small call).
/// `[ttl rq reps]`: parse and query files, median of `reps`.
pub fn run<E: Engine>(e: &E, args: &[String]) {
    if args.len() >= 2 && args[0] == "--small" {
        let n: u32 = args[1].parse().expect("N");
        let t = Instant::now();
        let mut len = 0;
        for _ in 0..n { len = e.query(SAMPLE_TTL, SAMPLE_RQ).len(); }
        eprintln!("small_call_us={:.2} answer_bytes={len}", t.elapsed().as_secs_f64() * 1e6 / n as f64);
        return;
    }
    if args.len() < 2 {
        match e.turtle_to_nquads(SAMPLE_TTL) {
            Ok(nq) => print!("{nq}"),
            Err(err) => eprintln!("error: {err}"),
        }
        println!("{}", e.query(SAMPLE_TTL, SAMPLE_RQ));
        return;
    }
    let ttl = std::fs::read_to_string(&args[0]).expect("read Turtle file");
    let rq = std::fs::read_to_string(&args[1]).expect("read SPARQL file");
    let reps: usize = args.get(2).map(|s| s.parse().expect("reps")).unwrap_or(1);
    let median = |mut v: Vec<f64>| { v.sort_by(|a, b| a.partial_cmp(b).unwrap()); v[v.len() / 2] };
    let (mut ps, mut qs, mut nq_len, mut ans) = (vec![], vec![], 0, String::new());
    for _ in 0..reps {
        let t = Instant::now();
        nq_len = e.turtle_to_nquads(&ttl).map(|s| s.len()).unwrap_or(0);
        ps.push(t.elapsed().as_secs_f64() * 1e3);
        let t = Instant::now();
        ans = e.query(&ttl, &rq);
        qs.push(t.elapsed().as_secs_f64() * 1e3);
    }
    println!("{ans}");
    eprintln!("parse_ms={:.1} query_ms={:.1} nquads_bytes={nq_len} first_parse_ms={:.1} first_query_ms={:.1}",
              median(ps.clone()), median(qs.clone()), ps[0], qs[0]);
}
