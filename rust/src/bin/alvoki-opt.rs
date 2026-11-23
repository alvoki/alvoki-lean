use alvoki_block::{Block, encode};
use std::{env, fs, hint::black_box, time::Instant};

#[inline]
fn word(bytes: &[u8], offset: usize) -> u64 {
    u64::from_le_bytes(bytes[offset..offset + 8].try_into().unwrap())
}

struct View<'a> {
    bytes: &'a [u8],
    count: usize,
    stride: usize,
    values: usize,
}

impl<'a> View<'a> {
    fn parse(bytes: &'a [u8]) -> Result<Self, &'static str> {
        let payload = bytes.len().checked_sub(16).ok_or("short header")?;
        let count = payload / 16;
        if payload % 16 != 0 || word(bytes, 0) != count as u64 {
            return Err("invalid length");
        }
        let (stride, values) = match word(bytes, 8) {
            1 => (16, 24),
            2 => (8, 16 + count * 8),
            _ => return Err("invalid header"),
        };
        let view = Self { bytes, count, stride, values };
        if count > 0 {
            let mut previous = view.key(0);
            for index in 1..count {
                let key = view.key(index);
                if previous >= key {
                    return Err("keys must increase");
                }
                previous = key;
            }
        }
        Ok(view)
    }

    #[inline]
    fn key(&self, index: usize) -> u64 {
        word(self.bytes, 16 + index * self.stride)
    }

    #[inline]
    fn value(&self, index: usize) -> u64 {
        word(self.bytes, self.values + index * self.stride)
    }

    fn lower_bound(&self, target: u64) -> usize {
        let mut lo = 0;
        let mut hi = self.count;
        while lo < hi {
            let mid = lo + (hi - lo) / 2;
            if self.key(mid) < target {
                lo = mid + 1;
            } else {
                hi = mid;
            }
        }
        lo
    }

    fn lookup_at(&self, index: usize, key: u64) -> Option<u64> {
        (index < self.count && self.key(index) == key).then(|| self.value(index))
    }

    fn scan(&self, lo: usize, hi: usize) -> u64 {
        (lo..hi).fold(0u64, |sum, i| sum.wrapping_add(self.key(i) ^ self.value(i)))
    }
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let args: Vec<_> = env::args().skip(1).collect();
    let [mode, input, query, param, reps] = args.as_slice() else {
        return Err("expected experiment input queries width repetitions".into());
    };
    let bytes = fs::read(input)?;
    let view = View::parse(&bytes)?;
    let queries = Block::parse(&fs::read(query)?)?.decode();
    let baseline = if mode == "decode-pair" { Some(Block::parse(&bytes)?) } else { None };
    let records = if mode == "write-wide" { Block::parse(&bytes)?.decode() } else { Vec::new() };
    let width: u64 = param.parse()?;
    for _ in 0..reps.parse()? {
        let start = Instant::now();
        let sum = match mode.as_str() {
            "validate-machine" => View::parse(black_box(&bytes))?.count as u64,
            "decode-pair" => black_box(black_box(baseline.as_ref().unwrap()).decode()).iter()
                .fold(0u64, |sum, &(k, v)| sum.wrapping_add(k ^ v)),
            "stream-machine" => view.scan(0, view.count),
            "point-machine" => queries.iter().fold(0u64, |sum, &(_, key)| {
                sum.wrapping_add(view.lookup_at(view.lower_bound(key), key).unwrap_or(0))
            }),
            "range-machine" | "check" => {
                let mut sum = 0u64;
                for &(_, key) in &queries {
                    let lo = view.lower_bound(key);
                    let hi = view.lower_bound(key.saturating_add(width));
                    let scan = view.scan(lo, hi);
                    if mode == "check" {
                        let hit = view.lookup_at(lo, key).map_or("-".to_owned(), |x| x.to_string());
                        println!("{hit} {lo} {hi} {scan}");
                    }
                    sum = sum.wrapping_add(scan);
                }
                sum
            }
            "read-wide" => (0..view.count).fold(0u64, |sum, i| {
                sum.wrapping_add(word(&bytes, 17 + i * 16))
            }),
            "write-wide" => word(black_box(&encode(black_box(&records))), 8),
            _ => return Err("unknown experiment".into()),
        };
        if mode != "check" {
            println!("{} {}", start.elapsed().as_nanos(), black_box(sum));
        }
    }
    if env::var_os("ALVOKI_RSS").is_some() {
        let status = fs::read_to_string("/proc/self/status")?;
        let peak = status.lines().find(|line| line.starts_with("VmHWM:")).ok_or("missing VmHWM")?;
        println!("{peak}");
    }
    Ok(())
}
