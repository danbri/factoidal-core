// @factoidal/core/sample-store (Node only): a small store packed on demand.
/** The triples of the sample store, as Turtle. */
export const SAMPLE_TURTLE: string;
/** What the sample store holds. */
export const sampleStoreFacts: Readonly<{ triples: number; source: string; layout: string }>;
/** Pack the sample store under `dir` (or a new temporary directory) unless it holds CURRENT; return the root. */
export function sampleStorePath(dir?: string): string;
export default sampleStorePath;
