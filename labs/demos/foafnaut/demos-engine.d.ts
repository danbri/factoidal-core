export interface DemosModule {
  ccall(name: string, result: "number", types: string[], values: (string | number)[]): number;
  ccall(name: string, result: null, types: string[], values: (string | number)[]): void;
  UTF8ToString(pointer: number): string;
}
export default function createModule(): Promise<DemosModule>;
