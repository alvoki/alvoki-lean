use std::{env, fs, hint::black_box, time::Instant};

const HEADER: usize = 16;
const WIDTH: usize = 32;

#[inline]
fn word(bytes: &[u8], offset: usize) -> u64 {
    u64::from_le_bytes(bytes[offset..offset + 8].try_into().unwrap())
}

#[derive(Clone, Copy)]
struct Run<'a>(&'a [u8]);

impl<'a> Run<'a> {
    fn parse(bytes: &'a [u8]) -> Result<Self, &'static str> {
        if bytes.len() < HEADER || word(bytes, 8) != 3 {
            return Err("expected a versioned run");
        }
        let rows = &bytes[HEADER..];
        if rows.len() % WIDTH != 0 || word(bytes, 0) != (rows.len() / WIDTH) as u64 {
            return Err("invalid versioned run length");
        }
        let mut previous = None;
        for row in rows.chunks_exact(WIDTH) {
            let (key, seq, kind) = (word(row, 0), word(row, 8), word(row, 16));
            if kind > 1 || (kind == 1 && word(row, 24) != 0) {
                return Err("invalid row kind");
            }
            if let Some((p, s)) = previous {
                if key < p || (key == p && seq >= s) {
                    return Err("invalid version order");
                }
            }
            previous = Some((key, seq));
        }
        Ok(Self(rows))
    }

    #[inline]
    fn row(self, index: usize) -> &'a [u8] {
        &self.0[WIDTH * index..WIDTH * (index + 1)]
    }
}

fn visit(left: Run<'_>, right: Run<'_>, floor: u64, mut emit: impl FnMut(bool, usize, u64, u64)) {
    let (mut i, mut j) = (0, 0);
    let mut previous = 0;
    let mut covered = false;
    while i < left.0.len() / WIDTH || j < right.0.len() / WIDTH {
        let a = (i < left.0.len() / WIDTH).then(|| left.row(i));
        let b = (j < right.0.len() / WIDTH).then(|| right.row(j));
        let (rightward, index, key, seq) = match (a, b) {
            (Some(a), Some(b)) => {
                let (ka, sa, kb, sb) = (word(a, 0), word(a, 8), word(b, 0), word(b, 8));
                if ka < kb || (ka == kb && sa > sb) {
                    i += 1;
                    (false, i - 1, ka, sa)
                } else {
                    i += usize::from(ka == kb && sa == sb);
                    j += 1;
                    (true, j - 1, kb, sb)
                }
            }
            (Some(a), None) => {
                i += 1;
                (false, i - 1, word(a, 0), word(a, 8))
            }
            (None, Some(b)) => {
                j += 1;
                (true, j - 1, word(b, 0), word(b, 8))
            }
            (None, None) => unreachable!(),
        };
        if key != previous || !covered {
            emit(rightward, index, key, seq);
        }
        previous = key;
        covered = seq <= floor;
    }
}

fn compact<const SPANS: bool>(left: Run<'_>, right: Run<'_>, floor: u64) -> Vec<u8> {
    let mut out = Vec::with_capacity(HEADER + left.0.len() + right.0.len());
    out.extend_from_slice(&0u64.to_le_bytes());
    out.extend_from_slice(&3u64.to_le_bytes());
    if SPANS {
        let mut pending = None;
        let mut flush = |(side, start, stop)| {
            let run = if side { right } else { left };
            out.extend_from_slice(&run.0[WIDTH * start..WIDTH * stop]);
        };
        visit(left, right, floor, |side, index, _, _| {
            if let Some((old_side, start, stop)) = pending {
                if side == old_side && index == stop {
                    pending = Some((side, start, index + 1));
                    return;
                }
                flush((old_side, start, stop));
            }
            pending = Some((side, index, index + 1));
        });
        if let Some(span) = pending {
            flush(span);
        }
    } else {
        visit(left, right, floor, |side, index, _, _| {
            let run = if side { right } else { left };
            out.extend_from_slice(run.row(index));
        });
    }
    let count = ((out.len() - HEADER) / WIDTH) as u64;
    out[..8].copy_from_slice(&count.to_le_bytes());
    out
}

fn scan(left: Run<'_>, right: Run<'_>, snapshot: u64) -> u64 {
    let mut sum = 0u64;
    visit(left, right, snapshot, |side, index, key, seq| {
        let row = if side { right.row(index) } else { left.row(index) };
        if seq <= snapshot && word(row, 16) == 0 {
            sum = sum.wrapping_add(key ^ word(row, 24));
        }
    });
    sum
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let args: Vec<_> = env::args().skip(1).collect();
    let [mode, left, right, floor, snapshot, output, trials] = args.as_slice() else {
        return Err("expected mode left right floor snapshot output trials".into());
    };
    let floor: u64 = floor.parse()?;
    let snapshot: u64 = snapshot.parse()?;
    if snapshot < floor {
        return Err("invalid snapshot bounds".into());
    }
    let left = fs::read(left)?;
    let right = fs::read(right)?;
    let left = Run::parse(&left)?;
    let right = Run::parse(&right)?;
    for _ in 0..trials.parse()? {
        let (a, b, floor, snapshot) = black_box((left, right, floor, snapshot));
        let start = Instant::now();
        let (bytes, sum) = match mode.as_str() {
            "rows" | "check-rows" => (compact::<false>(a, b, floor), 0),
            "spans" | "check-spans" => (compact::<true>(a, b, floor), 0),
            "direct" => (Vec::new(), scan(a, b, snapshot)),
            "pipeline" => {
                let output = compact::<true>(a, b, floor);
                (Vec::new(), scan(Run::parse(&output)?, Run(&[]), snapshot))
            }
            _ => return Err("invalid compaction mode".into()),
        };
        black_box(&bytes);
        let elapsed = start.elapsed().as_nanos();
        if mode.starts_with("check-") {
            fs::write(output, bytes)?;
        } else {
            let tag = if bytes.is_empty() {
                sum
            } else {
                word(&bytes, 0) ^ word(&bytes, bytes.len() - 8) ^ bytes.len() as u64
            };
            println!("{elapsed} {}", black_box(tag));
        }
    }
    Ok(())
}
