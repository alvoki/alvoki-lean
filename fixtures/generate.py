import random
import struct

WORD_MASK = (1 << 64) - 1
RECORD = struct.Struct("<QQ")


def block(records):
    return RECORD.pack(len(records), 1) + b"".join(RECORD.pack(*r) for r in records)


def columnar(records):
    return (RECORD.pack(len(records), 2)
            + b"".join(key.to_bytes(8, "little") for key, _ in records)
            + b"".join(value.to_bytes(8, "little") for _, value in records))


def dataset(size):
    return [(i * 2, i * 0x9E3779B97F4A7C15 & WORD_MASK) for i in range(size)]


def workloads(size, count=20_000):
    rng = random.Random(173)
    indices = [rng.randrange(size) for _ in range(count)]
    return {
        "hit": [i * 2 for i in indices],
        "miss": [i * 2 + 1 for i in indices],
        "mixed": [i * 2 + rng.randrange(2) for i in indices],
        "sequential": [i % size * 2 for i in range(count)],
        "large": [i * 2 for i in indices[:400]],
    }
