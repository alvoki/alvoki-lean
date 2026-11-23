use alvoki_block::Block;
use std::{env, fs, hint::black_box, time::Instant};

fn load(bytes: &[u8]) -> Result<Block<'_>, &'static str> {
    Block::parse(bytes)
}

fn fold(bytes: &[u8]) -> u64 {
    bytes.chunks_exact(16).fold(0u64, |sum, pair| {
        let key = u64::from_le_bytes(pair[..8].try_into().unwrap());
        let value = u64::from_le_bytes(pair[8..].try_into().unwrap());
        sum.wrapping_add(key ^ value)
    })
}

fn key(bytes: &[u8], index: usize) -> u64 {
    let start = 16 + index * 16;
    u64::from_le_bytes(bytes[start..start + 8].try_into().unwrap())
}

fn merge(left: &[u8], right: &[u8]) -> Vec<u8> {
    let n = (left.len() - 16) / 16;
    let m = (right.len() - 16) / 16;
    let mut out = Vec::with_capacity(left.len() + right.len() - 16);
    out.extend_from_slice(&0u64.to_le_bytes());
    out.extend_from_slice(&1u64.to_le_bytes());
    let (mut i, mut j) = (0, 0);
    while i < n && j < m {
        use std::cmp::Ordering;
        match key(left, i).cmp(&key(right, j)) {
            Ordering::Less => {
                let offset = 16 + 16 * i;
                out.extend_from_slice(&left[offset..offset + 16]);
                i += 1;
            }
            order => {
                let offset = 16 + 16 * j;
                out.extend_from_slice(&right[offset..offset + 16]);
                j += 1;
                i += usize::from(order == Ordering::Equal);
            }
        }
    }
    out.extend_from_slice(&left[16 + 16 * i..]);
    out.extend_from_slice(&right[16 + 16 * j..]);
    let count = ((out.len() - 16) / 16) as u64;
    out[..8].copy_from_slice(&count.to_le_bytes());
    out
}

fn fast_merge(left: &[u8], right: &[u8]) -> Vec<u8> {
    let n = (left.len() - 16) / 16;
    let m = (right.len() - 16) / 16;
    if n == 0 {
        return right.to_vec();
    }
    if m == 0 {
        return left.to_vec();
    }
    let (first, second) = if key(left, n - 1) < key(right, 0) {
        (left, right)
    } else if key(right, m - 1) < key(left, 0) {
        (right, left)
    } else {
        return merge(left, right);
    };
    let mut out = Vec::with_capacity(first.len() + second.len() - 16);
    out.extend_from_slice(&((n + m) as u64).to_le_bytes());
    out.extend_from_slice(&1u64.to_le_bytes());
    out.extend_from_slice(&first[16..]);
    out.extend_from_slice(&second[16..]);
    out
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let args: Vec<_> = env::args().skip(1).collect();
    let [mode, input, aux, output, repeats] = args.as_slice() else {
        return Err("expected mode input auxiliary output repetitions".into());
    };
    let bytes = fs::read(input)?;
    let run = load(&bytes)?;
    let other = if mode.ends_with("merge") || mode.starts_with("lookup") {
        let other = fs::read(aux)?;
        load(&other)?;
        other
    } else {
        Vec::new()
    };
    let records = if mode == "encode" || mode == "fill" {
        run.decode()
    } else {
        Vec::new()
    };
    let chunks: Vec<_> = if mode == "chunk-scan" {
        bytes[16..].chunks(4096).map(<[u8]>::to_vec).collect()
    } else {
        Vec::new()
    };
    for _ in 0..repeats.parse()? {
        let mut data = if mode == "fill" { vec![0; bytes.len()] } else { Vec::new() };
        let start = Instant::now();
        let source = black_box(&bytes);
        let checksum = match mode.as_str() {
            "retain-scan" => fold(&source[16..]),
            "copy-scan" => {
                data = source.to_vec();
                fold(&black_box(&data)[16..])
            }
            "owned-scan" => {
                black_box(black_box(&run).decode()).iter().fold(0u64, |sum, &(k, v)| {
                    sum.wrapping_add(k ^ v)
                })
            }
            "chunk-build-scan" => {
                let parts: Vec<_> = source[16..].chunks(4096).map(<[u8]>::to_vec).collect();
                black_box(&parts).iter().map(|part| fold(part)).fold(0u64, u64::wrapping_add)
            }
            "chunk-scan" => black_box(&chunks).iter().map(|part| fold(part))
                .fold(0u64, u64::wrapping_add),
            "lookup-packed" => {
                other[16..].chunks_exact(16).fold(0u64, |sum, pair| {
                    let target = u64::from_le_bytes(pair[8..].try_into().unwrap());
                    sum.wrapping_add(run.lookup(target).unwrap_or(0))
                })
            }
            "merge" | "check-merge" => {
                data = merge(source, black_box(&other));
                0
            }
            "fast-merge" | "check-fast-merge" => {
                data = fast_merge(source, black_box(&other));
                0
            }
            "encode" => {
                data = alvoki_block::encode(black_box(&records));
                0
            }
            "fill" => {
                data[..8].copy_from_slice(&(records.len() as u64).to_le_bytes());
                data[8..16].copy_from_slice(&1u64.to_le_bytes());
                for (dest, &(key, value)) in data[16..].chunks_exact_mut(16).zip(black_box(&records)) {
                    dest[..8].copy_from_slice(&key.to_le_bytes());
                    dest[8..].copy_from_slice(&value.to_le_bytes());
                }
                0
            }
            "init" => {
                data = vec![0; source.len()];
                0
            }
            _ => return Err("unknown packed experiment".into()),
        };
        black_box(&data);
        let elapsed = start.elapsed().as_nanos();
        if mode.starts_with("check-") {
            fs::write(output, &data)?;
        } else {
            let tag = if mode != "copy-scan" && data.len() >= 16 {
                let first = u64::from_le_bytes(data[..8].try_into().unwrap());
                let last = u64::from_le_bytes(data[data.len() - 8..].try_into().unwrap());
                first ^ last ^ data.len() as u64
            } else {
                checksum
            };
            println!("{elapsed} {}", black_box(tag));
        }
    }
    if env::var_os("ALVOKI_RSS").is_some() {
        let status = fs::read_to_string("/proc/self/status")?;
        println!("{}", status.lines().find(|s| s.starts_with("VmHWM:")).ok_or("missing VmHWM")?);
    }
    Ok(())
}
