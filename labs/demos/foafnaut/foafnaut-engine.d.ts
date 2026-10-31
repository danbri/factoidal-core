type Module = {
  ccall(name: string, result: string | null, types: string[], values: (string | number)[]): number;
  UTF8ToString(pointer: number): string;
};
export default function createModule(): Promise<Module>;
