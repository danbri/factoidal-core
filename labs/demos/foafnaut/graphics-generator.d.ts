// Public shim ABI only. Generated Emscripten internals stay outside type checking.
export interface GraphicsModule {
  ccall(name: string, result: "number", types: string[], values: number[]): number;
  ccall(name: string, result: null, types: string[], values: number[]): void;
  UTF8ToString(pointer: number): string;
}
export default function createModule(): Promise<GraphicsModule>;
