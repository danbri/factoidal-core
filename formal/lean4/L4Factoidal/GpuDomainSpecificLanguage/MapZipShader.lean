/-!
# The production PVGraph map/zip shader

The four storage slots are the existing PVGraph host ABI. All five branches
remain in one module so that WebGPU's automatic layout includes both inputs.
`MapZipSurface` parses these exact bytes and gives their invocation semantics.
The remaining word and scan kernels are separate modules in `GpuPlan`.
-/

namespace L4Factoidal.GpuDomainSpecificLanguage.MapZipShader

/-- WGSL compute source for the five common wrapping-u32 map/zip operations.
    WGSL sections: storage address space, integer arithmetic, if statements,
    global_invocation_id and workgroup_size. -/
def source : String := String.intercalate "\n" [
  "@group(0) @binding(0) var<storage, read> a : array<u32>;",
  "@group(0) @binding(1) var<storage, read> b : array<u32>;",
  "@group(0) @binding(2) var<storage, read_write> outWords : array<u32>;",
  "@group(0) @binding(3) var<storage, read> config : array<u32>;",
  "@compute @workgroup_size(64,1,1)",
  "fn main(@builtin(global_invocation_id) pv_gid : vec3<u32>) {",
  "  if (pv_gid.x < config[1u]) {",
  "    if (config[0u] == 1u) { outWords[pv_gid.x] = (a[pv_gid.x] + config[2u]); }",
  "    else if (config[0u] == 2u) { outWords[pv_gid.x] = (a[pv_gid.x] * config[2u]); }",
  "    else if (config[0u] == 3u) { outWords[pv_gid.x] = (a[pv_gid.x] ^ config[2u]); }",
  "    else if (config[0u] == 4u) { outWords[pv_gid.x] = (a[pv_gid.x] + b[pv_gid.x]); }",
  "    else if (config[0u] == 5u) { outWords[pv_gid.x] = (a[pv_gid.x] ^ b[pv_gid.x]); }",
  "  }",
  "}"
]

end L4Factoidal.GpuDomainSpecificLanguage.MapZipShader
