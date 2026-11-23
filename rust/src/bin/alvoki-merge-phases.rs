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

fn consume_winners(
    left: &Run<'_>,
    right: &Run<'_>,
    consume: impl Fn(u64, u64, u64) -> u64,
) -> u64 {
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

fn select(left: &Run<'_>, right: &Run<'_>) -> u64 {
    consume_winners(left, right, consume)
}

fn scan_selected(left: &Run<'_>, right: &Run<'_>) -> u64 {
    let (mut i, mut j, mut sum) = (0, 0, 0u64);
    while i < left.limit && j < right.limit {
        let a = left.key(i);
        let b = right.key(j);
        let (source, index, key) = if a < b { (left, i, a) } else { (right, j, b) };
        sum = sum.wrapping_add(key ^ source.value(index));
        i += usize::from(a <= b);
        j += usize::from(b <= a);
    }
    for index in i..left.limit {
        sum = sum.wrapping_add(left.key(index) ^ left.value(index));
    }
    for index in j..right.limit {
        sum = sum.wrapping_add(right.key(index) ^ right.value(index));
    }
    sum
}

fn validate_merge_trace(trace: &[u8], left: &Run<'_>, right: &Run<'_>) -> bool {
    let (mut i, mut j) = (0, 0);
    for &op in trace {
        let expected = match (i < left.limit, j < right.limit) {
            (true, true) => match left.key(i).cmp(&right.key(j)) {
                std::cmp::Ordering::Less => 0,
                std::cmp::Ordering::Greater => 1,
                std::cmp::Ordering::Equal => 2,
            },
            (true, false) => 0,
            (false, true) => 1,
            (false, false) => return false,
        };
        if op != expected {
            return false;
        }
        i += usize::from(op != 1);
        j += usize::from(op != 0);
    }
    i == left.limit && j == right.limit
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

/// Match the stock Lean fused emitter's eight-record probe and bounded window.
fn winning_end(run: &Run<'_>, start: usize, rival: u64, consecutive: bool) -> usize {
    if !consecutive || run.limit - start < 8 || run.key(start + 7) >= rival {
        return start + 1;
    }
    let stop = start + (run.limit - start).min(256);
    if run.key(stop - 1) < rival {
        return stop;
    }
    let (mut lo, mut hi) = (start + 8, stop);
    while lo < hi {
        let mid = lo + (hi - lo) / 2;
        if run.key(mid) < rival {
            lo = mid + 1;
        } else {
            hi = mid;
        }
    }
    lo
}

fn span_merge(left: &Run<'_>, right: &Run<'_>) -> Vec<u8> {
    let mut out = header(left.limit + right.limit, 0);
    let (mut i, mut j, mut last) = (0, 0, 2);
    while i < left.limit && j < right.limit {
        let a = left.key(i);
        let b = right.key(j);
        if a < b {
            let stop = winning_end(left, i, b, last == 0);
            out.extend_from_slice(&left.payload[16 * i..16 * stop]);
            i = stop;
            last = 0;
        } else if a == b {
            out.extend_from_slice(right.record(j));
            i += 1;
            j += 1;
            last = 2;
        } else {
            let stop = winning_end(right, j, a, last == 1);
            out.extend_from_slice(&right.payload[16 * j..16 * stop]);
            j = stop;
            last = 1;
        }
    }
    out.extend_from_slice(&left.payload[16 * i..]);
    out.extend_from_slice(&right.payload[16 * j..]);
    let count = ((out.len() - 16) / 16) as u64;
    out[..8].copy_from_slice(&count.to_le_bytes());
    out
}

fn copy_groups<const WIDTH: usize>(left: &Run<'_>, right: &Run<'_>, trace: &[u8], mut out: Vec<u8>) -> Vec<u8> {
    out[..8].copy_from_slice(&((left.limit + right.limit) as u64).to_le_bytes());
    out[8..16].copy_from_slice(&1u64.to_le_bytes());
    let (mut i, mut j) = (0, 0);
    for (&op, dst) in trace.iter().zip(out[16..].chunks_exact_mut(WIDTH)) {
        let source = if op == 0 {
            let start = i;
            i += WIDTH;
            &left.payload[start..i]
        } else {
            let start = j;
            j += WIDTH;
            &right.payload[start..j]
        };
        dst.copy_from_slice(source);
    }
    out
}

fn validate_groups(trace: &[u8], left: usize, right: usize, width: usize) -> bool {
    let mut zeros: usize = 0;
    for &op in trace {
        match op {
            0 => zeros += 1,
            1 => (),
            _ => return false,
        }
    }
    zeros.checked_mul(width) == Some(left) && (trace.len() - zeros).checked_mul(width) == Some(right)
}

fn builder_merge(left: &Run<'_>, right: &Run<'_>) -> Vec<u8> {
    let mut out = header(left.limit + right.limit, 0);
    // Each input cursor stays within its validated payload or one past it.
    // Advancing at least one cursor per emit bounds the writes by capacity.
    unsafe {
        let mut a = left.payload.as_ptr();
        let mut b = right.payload.as_ptr();
        let a_end = a.add(left.payload.len());
        let b_end = b.add(right.payload.len());
        let start = out.as_mut_ptr();
        let mut dst = start.add(16);
        while a < a_end && b < b_end {
            let key_a = u64::from_le(a.cast::<u64>().read_unaligned());
            let key_b = u64::from_le(b.cast::<u64>().read_unaligned());
            let source = if key_a < key_b { a } else { b };
            std::ptr::copy_nonoverlapping(source, dst, 16);
            a = a.add(16 * usize::from(key_a <= key_b));
            b = b.add(16 * usize::from(key_a >= key_b));
            dst = dst.add(16);
        }
        let a_len = a_end.offset_from(a) as usize;
        let b_len = b_end.offset_from(b) as usize;
        std::ptr::copy_nonoverlapping(a, dst, a_len);
        std::ptr::copy_nonoverlapping(b, dst.add(a_len), b_len);
        out.set_len(dst.offset_from(start) as usize + a_len + b_len);
    }
    let count = (out.len() - 16) / 16;
    out[..8].copy_from_slice(&(count as u64).to_le_bytes());
    out
}

/// Requires a fully consumed trace accepted by validate_merge_trace for these runs.
unsafe fn builder_replay(left: &Run<'_>, right: &Run<'_>, trace: &[u8]) -> Vec<u8> {
    let mut out = header(trace.len(), trace.len());
    let (mut i, mut j, mut dst) = (0, 0, 16);
    // The checked trace makes the source cursor valid on each access. The
    // destination is fresh, and exactly one record is initialized per op.
    unsafe {
        for &op in trace {
            let source = if op == 0 {
                left.payload.as_ptr().add(i)
            } else {
                right.payload.as_ptr().add(j)
            };
            std::ptr::copy_nonoverlapping(source, out.as_mut_ptr().add(dst), 16);
            i += 16 * usize::from(op != 1);
            j += 16 * usize::from(op != 0);
            dst += 16;
        }
        out.set_len(dst);
    }
    out
}

fn read_merged(bytes: &[u8], targets: Option<&Run<'_>>) -> Result<u64, &'static str> {
    let output = Block::parse(bytes)?;
    let mut sum = bytes[16..].chunks_exact(16).fold(0u64, |sum, record| {
        let key = u64::from_le_bytes(record[..8].try_into().unwrap());
        let value = u64::from_le_bytes(record[8..].try_into().unwrap());
        sum.wrapping_add(key ^ value)
    });
    if let Some(query) = targets {
        for i in 0..query.limit {
            sum = sum.wrapping_add(output.lookup(query.value(i)).unwrap_or(0));
        }
    }
    Ok(sum)
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let args: Vec<_> = env::args().skip(1).collect();
    let [mode, left, right, trace, output, repetitions] = args.as_slice() else {
        return Err("expected mode left right trace output repetitions".into());
    };
    let (scoped, mode) = match mode.strip_prefix("builder-") {
        Some(mode) => (true, mode),
        None => (false, mode.as_str()),
    };
    let left_bytes = fs::read(left)?;
    let right_bytes = fs::read(right)?;
    let left = Run::parse(&left_bytes)?;
    let right = Run::parse(&right_bytes)?;
    let operation = mode.strip_prefix("check-").unwrap_or(mode);
    let width = match operation {
        "copy16" => 16,
        "copy32" => 32,
        "copy64" => 64,
        "copy4096" => 4096,
        _ => 0,
    };
    let needs_trace = operation.starts_with("replay-");
    let needs_targets = matches!(mode, "pipeline" | "span-pipeline");
    let trace = if needs_trace || width != 0 || needs_targets {
        fs::read(trace)?
    } else {
        Vec::new()
    };
    let targets = if needs_targets { Some(Run::parse(&trace)?) } else { None };
    if (needs_trace && !validate_merge_trace(&trace, &left, &right))
        || (width != 0 && !validate_groups(&trace, left.limit, right.limit, width / 16))
    {
        return Err("invalid replay trace".into());
    }
    for _ in 0..repetitions.parse()? {
        let dest = if width == 0 { Vec::new() } else { vec![0xa5; left_bytes.len() + right_bytes.len() - 16] };
        black_box(&dest);
        let start = Instant::now();
        let (a, b, ops) = black_box((&left, &right, trace.as_slice()));
        let (bytes, sum) = match mode {
            "dense" | "check-dense" => {
                let mut bytes = black_box(left_bytes.as_slice()).to_vec();
                for row in bytes[16..].chunks_exact_mut(16) {
                    let value = u64::from_le_bytes(row[8..].try_into().unwrap()) ^ 0xfedcba9876543210;
                    row[8..].copy_from_slice(&value.to_le_bytes());
                }
                (bytes, 0)
            }
            "pipeline" | "merge-scan" => {
                let bytes = if scoped { builder_merge(a, b) } else { merge(a, b) };
                (Vec::new(), read_merged(&bytes, targets.as_ref())?)
            }
            "span-pipeline" | "span-merge-scan" =>
                (Vec::new(), read_merged(&span_merge(a, b), targets.as_ref())?),
            "selected-scan" => (Vec::new(), scan_selected(a, b)),
            "direct-scan" => (Vec::new(), consume_winners(a, b, |sum, k, v| sum.wrapping_add(k ^ v))),
            "select" => (Vec::new(), select(a, b)),
            "replay-checksum" => {
                let mut sum = 0;
                replay(a, b, ops, |run, i| sum = consume(sum, run.key(i), run.value(i)));
                (Vec::new(), sum)
            }
            "replay-write" | "check-replay-write" if scoped => {
                // Both runs and the trace were validated before timing.
                (unsafe { builder_replay(a, b, ops) }, 0)
            }
            "replay-write" | "check-replay-write" => {
                let mut out = header(ops.len(), ops.len());
                replay(a, b, ops, |run, i| out.extend_from_slice(run.record(i)));
                (out, 0)
            }
            "merge" | "check-merge" =>
                (if scoped { builder_merge(a, b) } else { merge(a, b) }, 0),
            "span-merge" | "check-span-merge" => (span_merge(a, b), 0),
            _ if width == 16 => (copy_groups::<16>(a, b, ops, dest), 0),
            _ if width == 32 => (copy_groups::<32>(a, b, ops, dest), 0),
            _ if width == 64 => (copy_groups::<64>(a, b, ops, dest), 0),
            _ if width == 4096 => (copy_groups::<4096>(a, b, ops, dest), 0),
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
    if env::var_os("ALVOKI_RSS").is_some() {
        let status = fs::read_to_string("/proc/self/status")?;
        let peak = status.lines().find(|line| line.starts_with("VmHWM:")).ok_or("missing VmHWM")?;
        println!("{peak}");
    }
    Ok(())
}
