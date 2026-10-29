//! wc-client: calls the Lean engine through the WIT interface
//! `factoidal:core/rdf` (https://github.com/danbri/factoidal/issues/1167).
//! A wasm32-wasip2 command component; composed with the engine by `wac plug`.
//! Arguments: see `bench::run`.
wit_bindgen::generate!({ path: "../wit", world: "client" });
mod bench;

use factoidal::core::rdf;

struct Component;
impl bench::Engine for Component {
    fn turtle_to_nquads(&self, ttl: &str) -> Result<String, String> { rdf::turtle_to_nquads(ttl, None) }
    fn query(&self, ttl: &str, rq: &str) -> String { rdf::query(ttl, rq) }
}

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    bench::run(&Component, &args);
}
