use alvoki_block::Block;
use std::{env, fs, hint::black_box, time::Instant};

struct Run<'a> {
    payload: &'a [u8],
    limit: usize,
}

impl<'a> Run<'a> {
    fn parse(bytes: &'a [u8]) -> Result<Self, &'static str> {
        Block::parse(bytes)?;
        let payload = &bytes[16..];
        Ok(Self { payload, limit: payload.len() / 16 })
    }

    #[inline]
    fn record(&self, index: usize) -> &[u8] {
        &self.payload[index * 16..(index + 1) * 16]
    }

    #[inline]
    fn key(&self, index: usize) -> u64 {
        u64::from_le_bytes(self.payload[index * 16..index * 16 + 8].try_into().unwrap())
    }

    #[inline]
    fn value(&self, index: usize) -> u64 {
        u64::from_le_bytes(self.payload[index * 16 + 8..(index + 1) * 16].try_into().unwrap())
    }
}

#[inline]
fn consume(sum: u64, key: u64, value: u64) -> u64 {
    sum.wrapping_mul(3).wrapping_add(key ^ value)
}

fn select(left: &Run<'_>, right: &Run<'_>) -> u64 {
    let (mut i, mut j, mut sum) = (0, 0, 0);
    while i < left.limit && j < right.limit {
        let a = left.key(i);
        let b = right.key(j);
        if a < b {
            sum = consume(sum, a, left.value(i));
            i += 1;
        } else {
            sum = consume(sum, b, right.value(j));
            i += usize::from(a == b);
            j += 1;
        }
    }
    for index in i..left.limit {
        sum = consume(sum, left.key(index), left.value(index));
    }
    for index in j..right.limit {
        sum = consume(sum, right.key(index), right.value(index));
    }
    sum
}

fn validate_trace(trace: &[u8], left: usize, right: usize) -> bool {
    let (mut i, mut j) = (0, 0);
    for &op in trace {
        match op {
            0 => i += 1,
            1 => j += 1,
            2 => {
                i += 1;
                j += 1;
            }
            _ => return false,
        }
        if i > left || j > right {
            return false;
        }
    }
    i == left && j == right
}

fn replay(left: &Run<'_>, right: &Run<'_>, trace: &[u8], mut emit: impl FnMut(&Run<'_>, usize)) {
    let (mut i, mut j) = (0, 0);
    for &op in trace {
        if op == 0 {
            emit(left, i);
            i += 1;
        } else {
            emit(right, j);
            i += usize::from(op == 2);
            j += 1;
        }
    }
}

fn header(capacity: usize, count: usize) -> Vec<u8> {
    let mut out = Vec::with_capacity(16 + 16 * capacity);
    out.extend_from_slice(&(count as u64).to_le_bytes());
    out.extend_from_slice(&1u64.to_le_bytes());
    out
}

fn merge(left: &Run<'_>, right: &Run<'_>) -> Vec<u8> {
    let mut out = header(left.limit + right.limit, 0);
    let (mut i, mut j) = (0, 0);
    while i < left.limit && j < right.limit {
        let a = left.key(i);
        let b = right.key(j);
        if a < b {
            out.extend_from_slice(left.record(i));
            i += 1;
        } else {
            out.extend_from_slice(right.record(j));
            i += usize::from(a == b);
            j += 1;
        }
    }
    out.extend_from_slice(&left.payload[16 * i..]);
    out.extend_from_slice(&right.payload[16 * j..]);
    let count = ((out.len() - 16) / 16) as u64;
    out[..8].copy_from_slice(&count.to_le_bytes());
    out
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let args: Vec<_> = env::args().skip(1).collect();
    let [mode, left, right, trace, output, repetitions] = args.as_slice() else {
        return Err("expected mode left right trace output repetitions".into());
    };
    let left_bytes = fs::read(left)?;
    let right_bytes = fs::read(right)?;
    let left = Run::parse(&left_bytes)?;
    let right = Run::parse(&right_bytes)?;
    let trace = fs::read(trace)?;
    if !validate_trace(&trace, left.limit, right.limit) {
        return Err("invalid replay trace".into());
    }
    for _ in 0..repetitions.parse()? {
        let start = Instant::now();
        let (a, b, ops) = black_box((&left, &right, trace.as_slice()));
        let (bytes, sum) = match mode.as_str() {
            "select" => (Vec::new(), select(a, b)),
            "replay-checksum" => {
                let mut sum = 0;
                replay(a, b, ops, |run, i| sum = consume(sum, run.key(i), run.value(i)));
                (Vec::new(), sum)
            }
            "replay-write" | "check-replay-write" => {
                let mut out = header(ops.len(), ops.len());
                replay(a, b, ops, |run, i| out.extend_from_slice(run.record(i)));
                (out, 0)
            }
            "merge" | "check-merge" => (merge(a, b), 0),
            _ => return Err("unknown mode".into()),
        };
        black_box(&bytes);
        let elapsed = start.elapsed().as_nanos();
        if mode.starts_with("check-") {
            fs::write(output, &bytes)?;
        } else {
            let tag = if bytes.len() >= 16 {
                u64::from_le_bytes(bytes[..8].try_into().unwrap())
                    ^ u64::from_le_bytes(bytes[bytes.len() - 8..].try_into().unwrap())
                    ^ bytes.len() as u64
            } else {
                sum
            };
            println!("{elapsed} {}", black_box(tag));
        }
    }
    Ok(())
}
