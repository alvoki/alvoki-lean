use std::{env, fs, hint::black_box, time::Instant};

const HEADER: usize = 16;
const ROW: usize = 32;
const MASK: u64 = 0xfedcba9876543210;

fn load(bytes: &[u8]) -> u64 {
    u64::from_le_bytes(bytes.try_into().unwrap())
}

fn payload(block: &[u8]) -> &[u8] {
    let rows = &block[HEADER..];
    assert_eq!(load(&block[8..16]), 3);
    assert_eq!(rows.len() % ROW, 0);
    assert_eq!(load(&block[..8]), (rows.len() / ROW) as u64);
    rows
}

#[inline(never)]
fn fresh(src: &[u8], out: &mut [u8]) {
    for (word, target) in src.chunks_exact(8).zip(out.chunks_exact_mut(8)) {
        target.copy_from_slice(&load(word).to_le_bytes());
    }
}

#[inline(never)]
fn dense(src: &[u8], out: &mut [u8]) {
    for (input, target) in src[HEADER..].chunks_exact(ROW).zip(out[HEADER..].chunks_exact_mut(ROW)) {
        if load(&input[16..24]) == 0 {
            target[24..32].copy_from_slice(&(load(&input[24..32]) ^ MASK).to_le_bytes());
        }
    }
}

#[inline(never)]
fn alternating(left: &[u8], right: &[u8], out: &mut [u8]) {
    out[..8].copy_from_slice(&(((left.len() + right.len()) / ROW) as u64).to_le_bytes());
    out[8..HEADER].copy_from_slice(&3u64.to_le_bytes());
    let mut target = out[HEADER..].chunks_exact_mut(ROW);
    let mut left = left.chunks_exact(ROW);
    for r in right.chunks_exact(ROW) {
        target.next().unwrap().copy_from_slice(left.next().unwrap());
        target.next().unwrap().copy_from_slice(r);
    }
    if let Some(tail) = left.next() {
        target.next().unwrap().copy_from_slice(tail);
    }
}

#[inline(never)]
fn owned(rows: &[[u64; 4]], out: &mut [u8]) {
    out[..8].copy_from_slice(&(rows.len() as u64).to_le_bytes());
    out[8..HEADER].copy_from_slice(&3u64.to_le_bytes());
    for (row, target) in rows.iter().zip(out[HEADER..].chunks_exact_mut(ROW)) {
        for (word, lane) in row.iter().zip(target.chunks_exact_mut(8)) {
            lane.copy_from_slice(&word.to_le_bytes());
        }
    }
}

fn main() {
    let args = env::args().skip(1).collect::<Vec<_>>();
    let [requested, left, right, output, trials] = args.as_slice() else {
        panic!("expected MODE LEFT RIGHT_OR_DASH OUT_OR_DASH TRIALS");
    };
    let (kernel, mode) = match requested.strip_prefix("kernel-") {
        Some(mode) => (true, mode),
        None => (false, requested.as_str()),
    };
    let left = fs::read(left).unwrap();
    let left_rows = payload(&left);
    let right = if mode == "alternating" {
        let right = fs::read(right).unwrap();
        let rows = payload(&right);
        assert!(left_rows.len() == rows.len() || left_rows.len() == rows.len() + ROW);
        right
    } else {
        Vec::new()
    };
    let right_rows = right.get(HEADER..).unwrap_or_default();
    let rows = if mode == "owned" {
        left_rows.chunks_exact(ROW).map(|row| {
            std::array::from_fn(|lane| load(&row[lane * 8..(lane + 1) * 8]))
        }).collect()
    } else {
        Vec::new()
    };
    let output_len = left.len() + right_rows.len();
    let prepare = || if mode == "dense" {
        left.clone()
    } else if kernel {
        // Force every output page to be resident outside the timed region.
        vec![0xa5; output_len]
    } else {
        vec![0; output_len]
    };
    for _ in 0..trials.parse::<usize>().unwrap() {
        let prepared = kernel.then(|| black_box(prepare()));
        let start = Instant::now();
        let mut bytes = prepared.unwrap_or_else(prepare);
        match mode {
            "fresh" => fresh(black_box(&left), &mut bytes),
            "dense" => dense(black_box(&left), &mut bytes),
            "alternating" => alternating(black_box(left_rows), black_box(right_rows), &mut bytes),
            "owned" => owned(black_box(&rows), &mut bytes),
            _ => panic!("unknown mode"),
        }
        let elapsed = start.elapsed().as_nanos();
        let tag = load(&bytes[..8]) ^ load(&bytes[bytes.len() - 8..]) ^ bytes.len() as u64;
        if output != "-" {
            fs::write(output, &bytes).unwrap();
        }
        println!("{elapsed} {tag}");
    }
}
