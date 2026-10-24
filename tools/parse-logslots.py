#!/usr/bin/env python3
# Decode the two log slots the XNU loader keeps in userdata (see xnuloader/loader.c,
# LOG_SLOT_*): a 48-byte header (magic "XNULOGSV", version, length, total, seq, uptime_ms,
# crc32) and then the text at offset 4096.
#
#   fastboot cannot read a partition back, and the MediaTek BROM is locked, so the slots
#   are normally read through the loader's own showprev=1 viewer.  Where the raw 4 MiB
#   region has been obtained some other way, this prints the headers and writes the
#   newest valid slot's text next to the input file.
#
# usage: parse-logslots.py logslots.bin
import os
import struct
import sys
import zlib

MAGIC = 0x5653474F4C554E58          # "XNULOGSV" little-endian
SLOT_SIZE = 0x200000
TEXT_OFF = 0x1000
HDR = struct.Struct("<QIIQQQII")    # 48 bytes


def main(path: str) -> int:
    data = open(path, "rb").read()
    print(f"{path}: {len(data)} bytes")
    best = None
    for slot in range(2):
        base = slot * SLOT_SIZE
        if base + HDR.size > len(data):
            print(f"slot {slot}: not in the file")
            continue
        magic, version, length, total, seq, uptime, crc, res = HDR.unpack_from(data, base)
        valid = magic == MAGIC and version == 1 and length <= SLOT_SIZE - TEXT_OFF
        print(f"slot {slot}: magic={magic:#018x} version={version} length={length} "
              f"total={total} seq={seq} uptime={uptime / 1000:.3f}s crc={crc:#010x} "
              f"{'valid header' if valid else 'NOT A SLOT'}")
        if not valid:
            continue
        text = data[base + TEXT_OFF: base + TEXT_OFF + length]
        crc_ok = (zlib.crc32(text) & 0xFFFFFFFF) == crc
        print(f"         crc {'OK' if crc_ok else 'MISMATCH'}")
        if best is None or seq > best[0]:
            best = (seq, slot, uptime, text, crc_ok, total)
    if best is None:
        print("no valid slot found")
        for slot in range(2):
            base = slot * SLOT_SIZE
            if base + 64 <= len(data):
                print(f"slot {slot} first 64 bytes: {data[base:base+64].hex()}")
        return 1
    seq, slot, uptime, text, crc_ok, total = best
    out = f"{path}.slot{slot}.log"
    open(out, "wb").write(text)
    print(f"\nnewest slot: {slot}, seq {seq}, saved at uptime {uptime / 1000:.1f}s, "
          f"loader_log then {total} bytes, crc {'OK' if crc_ok else 'BAD'}")
    print(f"text written to {out} ({len(text)} bytes)")
    text = text.replace(b"\r", b"")
    lines = text.decode("utf-8", "replace").splitlines()
    print(f"\n===== last 60 lines =====")
    for line in lines[-60:]:
        print(line)
    return 0


if __name__ == "__main__":
    if len(sys.argv) != 2:
        print("usage: parse-logslots.py logslots.bin", file=sys.stderr)
        sys.exit(2)
    sys.exit(main(sys.argv[1]))
