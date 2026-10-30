type Status = Pick<Deno.PermissionStatus,"state">;
export type NativePermissionAPI = {
  query(descriptor:Deno.FfiPermissionDescriptor):Promise<Status>;
  request(descriptor:Deno.FfiPermissionDescriptor):Promise<Status>;
};
// UnsafeWindowSurface requires this pathless permission even when the dylib is
// allowlisted. Resolve its existing prompt before creating/activating Cocoa UI.
export async function nativePreflight<T>(create:()=>T|Promise<T>,permissions:NativePermissionAPI=Deno.permissions):Promise<T> {
  const descriptor:Deno.FfiPermissionDescriptor={name:"ffi"};
  let status=await permissions.query(descriptor);
  if(status.state!=="granted")status=await permissions.request(descriptor);
  if(status.state!=="granted")throw new Error("Native surface FFI permission denied; no native window was created.");
  return await create();
}
