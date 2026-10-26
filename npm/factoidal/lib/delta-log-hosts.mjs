// Host stores for the durable update log (deltaLog* in lib/api.mjs; hub
// post 18; https://github.com/danbri/factoidal/issues/728).
//
// A host store keeps, for each log name, the records in commit order. A
// record is { seq, epoch, hex }: `hex` is the hexadecimal text of one DLB1
// record as the engine wrote it (op deltaLogEncode,
// formal/lean4/Wasm/Ops/DeltaLog.lean). The store does not read the hex.
// The byte format, the checksums, the torn-record rule and the merge are in
// Lean (formal/lean4/L4Factoidal/Storage/BrowserLog.lean); a host store
// only stores and loads text.
//
//   open(name)                 create the log if it is absent
//   append(name, makeRecord)   seq := the number of records; makeRecord(seq)
//                              (synchronous) gives {hex, epoch}; the record
//                              is committed with that seq, atomically
//   readAll(name)              the hex texts, in seq order
//   destroy(name)              remove the log
//   corruptLast(name)          TEST HOOK: cut the last 8 hex digits (4
//                              bytes) of the last record, as a torn write
//                              would; false when the log is empty
//
// No Node built-ins: the browser imports this file as it is.
import { hostError } from './errors.mjs';

const DELTA_STORE = 'deltaBatches';

/**
 * The records in the memory of this process. The default store of the Node
 * entry: the records live as long as the process. Pass another store to
 * buildApi() (driver.deltaLogStore) to keep them elsewhere.
 */
export function memoryDeltaLogStore() {
  const logs = new Map();
  const recordsOf = (name) => {
    if (!logs.has(name)) logs.set(name, []);
    return logs.get(name);
  };
  return {
    kind: 'memory',
    async open(name) {
      recordsOf(name);
    },
    async append(name, makeRecord) {
      const records = recordsOf(name);
      const seq = records.length;
      const rec = makeRecord(seq);
      records.push({ seq, epoch: rec.epoch, hex: rec.hex });
      return { seq };
    },
    async readAll(name) {
      return (logs.get(name) || []).map((r) => r.hex);
    },
    async destroy(name) {
      logs.delete(name);
    },
    async corruptLast(name) {
      const records = logs.get(name);
      if (!records || records.length === 0) return false;
      const last = records[records.length - 1];
      last.hex = last.hex.slice(0, Math.max(0, last.hex.length - 8));
      return true;
    },
  };
}

function indexedDbFactory() {
  const factory = globalThis.indexedDB;
  if (!factory) {
    throw hostError('deltaLog: this runtime has no indexedDB; the browser entry keeps the log in IndexedDB');
  }
  return factory;
}

function idbOpen(dbName) {
  return new Promise((resolve, reject) => {
    const req = indexedDbFactory().open(dbName, 1);
    req.onupgradeneeded = () => {
      const db = req.result;
      if (!db.objectStoreNames.contains(DELTA_STORE)) {
        db.createObjectStore(DELTA_STORE, { keyPath: 'seq' });
      }
    };
    req.onsuccess = () => resolve(req.result);
    req.onerror = () => reject(hostError('indexedDB.open failed', req.error));
    req.onblocked = () => reject(hostError('indexedDB.open blocked (another tab holds an open connection at an older version)'));
  });
}

function requestDone(req) {
  return new Promise((resolve, reject) => {
    req.onsuccess = () => resolve(req.result);
    req.onerror = () => reject(hostError('IndexedDB request failed', req.error));
  });
}

function transactionDone(tx) {
  return new Promise((resolve, reject) => {
    tx.oncomplete = () => resolve();
    tx.onerror = () => reject(hostError('IndexedDB transaction failed', tx.error));
    tx.onabort = () => reject(hostError('IndexedDB transaction aborted', tx.error));
  });
}

/**
 * The records in IndexedDB: one database for each log name, one object
 * store 'deltaBatches' keyed by seq, one object { seq, epoch, hex } for each
 * committed update. The default store of the browser entries.
 *
 * append() counts the records, calls makeRecord and adds the record in ONE
 * readwrite transaction. IndexedDB runs the readwrite transactions of one
 * object store one after another, so two tabs that append at the same time
 * get different seq values; `add` (not `put`) refuses a seq that exists. The
 * transaction asks for `durability: 'strict'`: Chrome 121 and later default
 * to 'relaxed', where `complete` can fire before the data is on disk.
 */
export function indexedDbDeltaLogStore() {
  return {
    kind: 'indexedDB',
    async open(name) {
      const db = await idbOpen(name);
      db.close();
    },
    async append(name, makeRecord) {
      const db = await idbOpen(name);
      try {
        const tx = db.transaction(DELTA_STORE, 'readwrite', { durability: 'strict' });
        const done = transactionDone(tx);
        const store = tx.objectStore(DELTA_STORE);
        let seq;
        let failure = null;
        const countReq = store.count();
        countReq.onsuccess = () => {
          seq = countReq.result;
          try {
            // Synchronous: the transaction stays active inside this callback.
            const rec = makeRecord(seq);
            store.add({ seq, epoch: rec.epoch, hex: rec.hex });
          } catch (err) {
            failure = err;
            tx.abort();
          }
        };
        try {
          await done;
        } catch (err) {
          throw failure || err;
        }
        return { seq };
      } finally {
        db.close();
      }
    },
    async readAll(name) {
      const db = await idbOpen(name);
      try {
        const all = await requestDone(
          db.transaction(DELTA_STORE, 'readonly').objectStore(DELTA_STORE).getAll());
        all.sort((a, b) => a.seq - b.seq);
        return all.map((r) => r.hex);
      } finally {
        db.close();
      }
    },
    async destroy(name) {
      await new Promise((resolve, reject) => {
        const req = indexedDbFactory().deleteDatabase(name);
        req.onsuccess = () => resolve();
        req.onerror = () => reject(hostError('indexedDB.deleteDatabase failed', req.error));
        req.onblocked = () => reject(hostError('indexedDB.deleteDatabase blocked (another open connection)'));
      });
    },
    async corruptLast(name) {
      const db = await idbOpen(name);
      try {
        const all = await requestDone(
          db.transaction(DELTA_STORE, 'readonly').objectStore(DELTA_STORE).getAll());
        if (all.length === 0) return false;
        all.sort((a, b) => a.seq - b.seq);
        const last = all[all.length - 1];
        const tx = db.transaction(DELTA_STORE, 'readwrite');
        const done = transactionDone(tx);
        tx.objectStore(DELTA_STORE).put({
          seq: last.seq, epoch: last.epoch, hex: last.hex.slice(0, Math.max(0, last.hex.length - 8)),
        });
        await done;
        return true;
      } finally {
        db.close();
      }
    },
  };
}
