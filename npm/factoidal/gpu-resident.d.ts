/**
 * Experimental, application-neutral GSSL GPU resource session.
 *
 * Does not implement SPARQL, an RDF store, shader verification, hardware
 * correctness or a browser Worklet API. Trusted WGSL code only.
 */
export interface ResidentSessionOptions {
  /** Existing WebGPU GPUDevice. Borrowed unless ownsDevice is true. */
  device?: unknown;
  /** Existing GPUAdapter or null to request one from navigator.gpu. */
  adapter?: unknown;
  /** Resident storage buffers, 4-byte aligned. Default 64 MiB, maximum 512 MiB. */
  byteBudget?: number;
  /** Maximum u32 words copied in one diagnostic request. Default 256. */
  inspectMaxWords?: number;
  /** Whether this session owns and may destroy a supplied GPUDevice. */
  ownsDevice?: boolean | null;
}
export interface UploadReport {
  id: string;
  sha256: string;
  uploaded: boolean;
  revision: number;
}
export interface GpuResourceBinding {
  /** WGSL @binding index in group 0. */
  binding: number;
  /** Previously uploaded or allocated resource identifier. */
  id: string;
}
export interface DispatchOptions {
  kernel: string;
  bindings: GpuResourceBinding[];
  /** Exactly the names of buffers the trusted shader may modify. */
  writes?: string[];
  workgroups?: [number, number, number];
}
export interface ResidentResourceReport {
  id: string;
  bytes: number;
  revision: number;
  initialized: boolean;
  dirty: boolean;
  /** SHA-256 for an untouched host upload, null after GPU writes. */
  sha256: string | null;
  usage: number;
}
export interface ResidentStatus {
  closed: boolean;
  lost: boolean;
  busy: boolean;
  usedBytes: number;
  byteBudget: number;
  resourceCount: number;
  kernelCount: number;
  createdPipelines: number;
  uploads: number;
  reuses: number;
  submissions: number;
  readbacks: number;
  generation: number;
  resources: ResidentResourceReport[];
}
export interface GsslResidentSession {
  allocate(id: string, byteLength: number, options?: {usage?: number}):
    {id: string; bytes: number};
  upload(id: string, input: ArrayBuffer | ArrayBufferView,
    options?: {usage?: number}): Promise<UploadReport>;
  compile(id: string, source: string, options?: {entryPoint?: string}):
    Promise<{id: string; compiled: boolean; sha256: string}>;
  dispatch(options: DispatchOptions): Promise<{
    kernel: string; submissions: number; revision: number;
    status: "observed-not-proven";
  }>;
  inspect(id: string, options?: {
    offsetWords?: number; countWords?: number;
  }): Promise<{id: string; offsetWords: number; words: number[]; revision: number}>;
  release(id: string): boolean;
  status(): ResidentStatus;
  close(): void;
}
export function createGsslResidentSession(
  options?: ResidentSessionOptions,
): Promise<GsslResidentSession>;
