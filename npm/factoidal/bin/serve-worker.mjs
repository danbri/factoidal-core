// The worker thread of `factoidal serve` (`listenOnWorker` in ./serve.mjs):
// the engine, the served store and the sockets live here, on a thread whose
// call stack the parent raised. This file starts `listen`, reports where it
// is listening, and closes on request. It decides nothing else.
import { parentPort, workerData } from 'node:worker_threads'
import { listen } from './serve.mjs'

let running = null
try {
  running = await listen(workerData.root, {
    ...workerData.options,
    onError: (error) => {
      console.error(`factoidal serve: ${error && error.message ? error.message : error}`)
    }
  })
  parentPort.postMessage({
    kind: 'listening', origin: running.origin, port: running.port, info: running.served.info
  })
} catch (error) {
  parentPort.postMessage({
    kind: 'error',
    message: error && error.message ? error.message : String(error),
    unknownOp: error && error.unknownOp === true
  })
}

parentPort.on('message', async (message) => {
  if (message && message.kind === 'close') {
    if (running !== null) await running.close()
    parentPort.postMessage({ kind: 'closed' })
  }
})
