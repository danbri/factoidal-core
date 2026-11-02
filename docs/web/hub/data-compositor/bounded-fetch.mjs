// Application transport budget, not an LWS protocol or authorization decision.
// Count delivered bytes rather than trusting Content-Length (compressed/chunked
// responses can differ). The browser may buffer internally before delivery.
export function boundedFetch(fetcher, maxBytes) {
  if (!Number.isSafeInteger(maxBytes) || maxBytes < 1) throw new TypeError('Invalid response byte limit.');
  return async (url, init) => {
    const response = await fetcher(url, init);
    const chunks = [];
    let size = 0;
    if (response.body) {
      const reader = response.body.getReader();
      try {
        while (true) {
          const {done, value} = await reader.read();
          if (done) break;
          size += value.byteLength;
          if (size > maxBytes) {
            await reader.cancel('Pod response exceeds application byte limit.').catch(() => {});
            throw new RangeError(`Pod response exceeds ${maxBytes} bytes.`);
          }
          chunks.push(value);
        }
      } finally { reader.releaseLock(); }
    }
    const bytes = new Uint8Array(size);
    let offset = 0;
    for (const chunk of chunks) { bytes.set(chunk, offset); offset += chunk.byteLength; }
    // These are exactly the response members consumed by the shared LWS host.
    return {status: response.status, headers: response.headers,
      arrayBuffer: async () => bytes.buffer};
  };
}
