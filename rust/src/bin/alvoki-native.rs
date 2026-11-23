use alvoki_block::Block;
use std::{env, fs, hint::black_box, time::Instant};

#[inline(never)]
fn scan(payload: &[u8]) -> u64 {
    payload.chunks_exact(16).fold(0, |sum: u64, record| {
        let key = u64::from_le_bytes(record[..8].try_into().unwrap());
        let value = u64::from_le_bytes(record[8..].try_into().unwrap());
        sum.wrapping_add(key ^ value)
    })
}

fn encode(source: &[u8], mask: u64) -> Vec<u8> {
    let mut out = Vec::with_capacity(source.len());
    out.extend_from_slice(&source[..16]);
    for record in source[16..].chunks_exact(16) {
        out.extend_from_slice(&record[..8]);
        let value = u64::from_le_bytes(record[8..].try_into().unwrap()) ^ mask;
        out.extend_from_slice(&value.to_le_bytes());
    }
    out
}

fn copy_patch_low(source: &[u8]) -> Vec<u8> {
    let mut result = source.to_vec();
    for record in result[16..].chunks_exact_mut(16) {
        record[8] ^= 1;
    }
    result
}

fn copy_patch(source: &[u8], mask: u64) -> Vec<u8> {
    let mut result = source.to_vec();
    for record in result[16..].chunks_exact_mut(16) {
        let value = u64::from_le_bytes(record[8..].try_into().unwrap()) ^ mask;
        record[8..].copy_from_slice(&value.to_le_bytes());
    }
    result
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let args: Vec<_> = env::args().skip(1).collect();
    let [mode, input, _auxiliary, output, repetitions] = args.as_slice() else {
        return Err("expected mode input auxiliary output repetitions".into());
    };
    let source = fs::read(input)?;
    Block::parse(&source)?;
    for _ in 0..repetitions.parse()? {
        let start = Instant::now();
        let data = black_box(source.as_slice());
        let (bytes, sum) = match mode.as_str() {
            "scan" => (Vec::new(), scan(&data[16..])),
            "encode" | "check-encode" => (encode(data, 1), 0),
            "encode-dense" | "check-encode-dense" => (encode(data, 0xfedcba9876543210), 0),
            "copy-low" | "check-copy-low" => (copy_patch_low(data), 0),
            "copy-dense" | "check-copy-dense" => (copy_patch(data, 0xfedcba9876543210), 0),
            _ => return Err("unknown experiment".into()),
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
