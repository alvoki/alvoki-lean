use std::{env, fs::{self, File}, io::{self, Read, Write}, path::{Path, PathBuf}, time::Instant};

fn syn(path: &Path) -> io::Result<()> {
    File::open(path).and_then(|file| file.sync_all())
        .map_err(|err| io::Error::new(err.kind(), format!("fsync {}: {err}", path.display())))
}

fn files(dir: &Path) -> io::Result<()> {
    syn(&dir.join("WAL"))?;
    syn(&dir.join("WAL.commit.next"))
}
fn worker(dir: &Path, once: bool) -> io::Result<()> {
    let mut request = [0];
    let mut input = io::stdin().lock();
    let mut output = io::stdout().lock();
    output.write_all(b"R")?;
    output.flush()?;
    let fail = env::var("ALVOKI_LATENCY_FAIL").unwrap_or_default();
    if fail == "start" { return Err(io::Error::other("injected child death")); }
    let mut stage = false;
    loop {
        if input.read(&mut request)? == 0 { return Ok(()); }
        match request[0] {
            b'F' if !stage => {
                syn(&dir.join("WAL"))?;
                if fail == "file" { return Err(io::Error::other("injected staged file fsync failure")); }
                syn(&dir.join("WAL.commit.next"))?;
            },
            b'D' if stage => {
                if fail == "directory" { return Err(io::Error::other("injected directory fsync failure")); }
                syn(dir)?;
            },
            _ => return Err(io::Error::other("out-of-order sync request")),
        }
        stage = !stage;
        output.write_all(b"Y")?;
        output.flush()?;
        if once && !stage { return Ok(()); }
    }
}

fn stats(dir: &Path, count: usize) -> io::Result<()> {
    let wal_path = dir.join("WAL");
    let stage = dir.join("WAL.commit.next");
    let active = dir.join("WAL.commit");
    File::create(&wal_path)?.sync_all()?;
    syn(dir)?;
    for i in 0..(count + 1) {
        let start = Instant::now();
        fs::OpenOptions::new().append(true).open(&wal_path)?.write_all(&[0u8;48])?;
        fs::write(&stage, [0u8;24])?;
        let prepared = start.elapsed().as_nanos();
        let t = Instant::now();
        syn(&wal_path)?;
        let wal_sync = t.elapsed().as_nanos();
        let t = Instant::now();
        syn(&stage)?;
        let stage_sync = t.elapsed().as_nanos();
        let t = Instant::now();
        fs::rename(&stage,&active)?;
        let rename = t.elapsed().as_nanos();
        let t = Instant::now();
        syn(dir)?;
        let dir_sync = t.elapsed().as_nanos();
        if i > 0 { println!("{prepared},{wal_sync},{stage_sync},{rename},{dir_sync}"); }
    }
    Ok(())
}

fn main() -> io::Result<()> {
    let mut args = env::args_os().skip(1);
    let mode = args.next().ok_or_else(|| io::Error::other("missing mode"))?;
    let dir = PathBuf::from(args.next().ok_or_else(|| io::Error::other("missing path"))?);
    match mode.to_str() {
        Some("once") => worker(&dir, true),
        Some("persistent") => worker(&dir, false),
        Some("direct") => {
            files(&dir)?;
            fs::rename(dir.join("WAL.commit.next"), dir.join("WAL.commit"))?;
            syn(&dir)
        },
        Some("stats") => {
            let count = args.next().unwrap().to_str().unwrap().parse().unwrap();
            stats(&dir,count)
        },
        Some("noop") => Ok(()),
        _ => Err(io::Error::other("invalid mode")),
    }
}
