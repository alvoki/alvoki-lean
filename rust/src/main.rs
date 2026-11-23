use alvoki_block::{Block, encode};
use std::{env, fs, hint::black_box, time::Instant};

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let args: Vec<_> = env::args().skip(1).collect();
    let [mode, input, query, param, repeats] = args.as_slice() else {
        return Err("expected mode input queries parameter repetitions".into());
    };
    let bytes = fs::read(input)?;
    let block = Block::parse(&bytes)?;
    if mode == "check" {
        fs::write(param, encode(&block.decode()))?;
    }
    let queries = Block::parse(&fs::read(query)?)?.decode();
    let repeats: usize = repeats.parse()?;
    let records = if mode == "encode" { block.decode() } else { Vec::new() };
    for _ in 0..repeats {
        let start = Instant::now();
        let mut sum = 0u64;
        match mode.as_str() {
            "encode" => sum = black_box(encode(black_box(&records))).len() as u64,
            "decode" => sum = black_box(black_box(&block).decode()).len() as u64,
            "load" => sum = Block::parse(&fs::read(input)?)?.len() as u64,
            "validate" => sum = black_box(Block::parse(black_box(&bytes))?).len() as u64,
            "point" => {
                for &(_, key) in &queries {
                    sum = sum.wrapping_add(block.lookup(key).unwrap_or(0));
                }
            }
            "range" | "check" => {
                let width: u64 = param.parse().unwrap_or(8);
                for &(_, key) in &queries {
                    let end = key.saturating_add(width);
                    let range = block.range_indices(key..end);
                    let mut scan = 0u64;
                    for (k, v) in block.iter_indices(range.clone()) {
                        scan = scan.wrapping_add(k ^ v);
                    }
                    if mode == "check" {
                        let value = block.lookup(key).map_or("-".to_owned(), |x| x.to_string());
                        println!("{value} {} {} {scan}", range.start, range.end);
                    }
                    sum = sum.wrapping_add(scan);
                }
            }
            _ => return Err("unknown mode".into()),
        }
        if mode != "check" {
            println!("{} {}", start.elapsed().as_nanos(), black_box(sum));
        }
    }
    if env::var_os("ALVOKI_RSS").is_some() {
        let status = fs::read_to_string("/proc/self/status")?;
        let peak = status.lines().find(|line| line.starts_with("VmHWM:"))
            .ok_or("missing VmHWM")?;
        println!("{peak}");
    }
    Ok(())
}
