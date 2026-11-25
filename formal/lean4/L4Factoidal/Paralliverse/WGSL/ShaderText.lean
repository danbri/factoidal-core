/-! # Static UTF-8 WGSL sources for stable packing

The restricted-language proofs and the Hub ABI consume these same constants. -/

namespace L4Factoidal.Paralliverse.WGSL

def countText : String := r#"@group(0) @binding(0) var<storage, read> src_words : array<u32>;
@group(0) @binding(2) var<storage, read_write> dst_words : array<u32>;
@compute @workgroup_size(64, 1, 1)
fn main(@builtin(global_invocation_id) pv_gid : vec3<u32>) {
  if (pv_gid.x < src_words[1u]) {
    dst_words[pv_gid.x] = src_words[(4u + (2u * pv_gid.x))];
  }
}
"#

def scanText : String := r#"@group(0) @binding(0) var<storage, read> src_words : array<u32>;
@group(0) @binding(1) var<storage, read> aux_words : array<u32>;
@group(0) @binding(2) var<storage, read_write> dst_words : array<u32>;
@compute @workgroup_size(1, 1, 1)
fn main(@builtin(global_invocation_id) pv_gid : vec3<u32>) {
  var pv_l0 : u32 = 0u;
  let pv_bound : u32 = src_words[1u];
  if (pv_bound > 128u) { return; }
  for (var pv_i : u32 = 0u; pv_i < pv_bound; pv_i = (pv_i + 1u)) {
    dst_words[pv_i] = pv_l0;
    pv_l0 = (pv_l0 + aux_words[pv_i]);
  }
  dst_words[src_words[1u]] = pv_l0;
}
"#

def scatterText : String := r#"@group(0) @binding(0) var<storage, read> src_words : array<u32>;
@group(0) @binding(1) var<storage, read> aux_words : array<u32>;
@group(0) @binding(2) var<storage, read_write> dst_words : array<u32>;
@compute @workgroup_size(64, 1, 1)
fn main(@builtin(global_invocation_id) pv_gid : vec3<u32>) {
  if (pv_gid.x < src_words[1u]) {
    var pv_l0 : u32 = (3u + (2u * src_words[1u]));
    var pv_l1 : u32 = src_words[(3u + (2u * pv_gid.x))];
    pv_l0 = (pv_l0 + pv_l1);
    pv_l1 = aux_words[pv_gid.x];
    let pv_bound : u32 = src_words[(4u + (2u * pv_gid.x))];
    if (pv_bound > 1024u) { return; }
    for (var pv_i : u32 = 0u; pv_i < pv_bound; pv_i = (pv_i + 1u)) {
      dst_words[(pv_l1 + pv_i)] = src_words[(pv_l0 + pv_i)];
    }
  }
}
"#

end L4Factoidal.Paralliverse.WGSL
