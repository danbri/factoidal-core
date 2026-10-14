#!/usr/bin/env python3
"""Change the bytes of a DLOG file (deltas.dlog) the way a crash or damage
would, for tests/delta-log/run.sh (https://github.com/danbri/factoidal/issues/843).

The format is Storage/DeltaLog.lean: an eight-byte header ('DLOG', version),
then DLB1 frames: magic 'DLB1', version u32 1, body length u32, body, checksum
u32 (the sum of the body bytes modulo 2^32). A body is seq u64, epoch u64,
entry count u32, then DLE1 entry frames of the same shape.

usage:
  dlog.py frames LOG                       print the offset and size of each frame
  dlog.py cut LOG N                        remove the last N bytes
  dlog.py bump LOG K OFFSET                add 1 to byte OFFSET of the body of
                                           frame K (1-based); its checksum fails
  dlog.py append-unknown LOG SEQ EPOCH     append a frame whose checksum verifies
                                           and whose one entry has the unknown
                                           entry tag 9
  dlog.py append-plain LOG SEQ EPOCH S P O append a frame with one INSERT DATA
                                           entry <S> <P> "O" in the default graph
"""
import struct
import sys


def u32(n):
    return struct.pack('<I', n)


def u64(n):
    return struct.pack('<Q', n)


def checksum(bs):
    return sum(bs) % (1 << 32)


def frame(magic, body):
    return magic + u32(1) + u32(len(body)) + body + u32(checksum(body))


def lstr(s):
    b = s.encode('utf-8')
    return u32(len(b)) + b


def frames(log):
    """(offset, size) of each complete frame after the header."""
    out = []
    pos = 8
    while pos + 12 <= len(log):
        (n,) = struct.unpack_from('<I', log, pos + 8)
        size = 16 + n
        if pos + size > len(log):
            break
        out.append((pos, size))
        pos += size
    return out


def batch(seq, epoch, entries):
    body = u64(seq) + u64(epoch) + u32(len(entries)) + b''.join(entries)
    return frame(b'DLB1', body)


def main():
    cmd, path = sys.argv[1], sys.argv[2]
    log = bytearray(open(path, 'rb').read())
    if cmd == 'frames':
        for i, (off, size) in enumerate(frames(log), 1):
            print(f'frame {i} offset {off} size {size}')
        return
    if cmd == 'cut':
        n = int(sys.argv[3])
        del log[len(log) - n:]
    elif cmd == 'bump':
        k, off = int(sys.argv[3]), int(sys.argv[4])
        start, size = frames(log)[k - 1]
        i = start + 12 + off
        if i >= start + size - 4:
            sys.exit('bump: offset is past the body')
        log[i] = (log[i] + 1) % 256
    elif cmd == 'append-unknown':
        seq, epoch = int(sys.argv[3]), int(sys.argv[4])
        log += batch(seq, epoch, [frame(b'DLE1', bytes([9]))])
    elif cmd == 'append-plain':
        seq, epoch = int(sys.argv[3]), int(sys.argv[4])
        s, p, o = sys.argv[5], sys.argv[6], sys.argv[7]
        literal = (bytes([2]) + lstr(o) + lstr('http://www.w3.org/2001/XMLSchema#string')
                   + bytes([0]))
        payload = bytes([0]) + bytes([0]) + lstr(s) + lstr(p) + literal + bytes([0])
        log += batch(seq, epoch, [frame(b'DLE1', payload)])
    else:
        sys.exit(f'unknown command {cmd}')
    open(path, 'wb').write(log)


main()
