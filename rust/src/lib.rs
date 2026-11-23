use std::ops::Range;

pub type Record = (u64, u64);

fn word(bytes: &[u8], offset: usize) -> u64 {
    u64::from_le_bytes(bytes[offset..offset + 8].try_into().unwrap())
}

pub struct Block<'a> {
    bytes: &'a [u8],
}

impl<'a> Block<'a> {
    pub fn parse(bytes: &'a [u8]) -> Result<Self, &'static str> {
        if bytes.len() < 16 || word(bytes, 8) != 1 {
            return Err("invalid header");
        }
        let payload = bytes.len() - 16;
        if payload % 16 != 0 || word(bytes, 0) != (payload / 16) as u64 {
            return Err("invalid length");
        }
        let block = Self { bytes };
        for index in 1..block.len() {
            if block.key(index - 1) >= block.key(index) {
                return Err("keys must increase");
            }
        }
        Ok(block)
    }

    pub fn len(&self) -> usize {
        (self.bytes.len() - 16) / 16
    }

    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    fn key(&self, index: usize) -> u64 {
        word(self.bytes, 16 + index * 16)
    }

    pub fn record(&self, index: usize) -> Record {
        (self.key(index), word(self.bytes, 24 + index * 16))
    }

    pub fn lower_bound(&self, key: u64) -> usize {
        let mut lo = 0;
        let mut hi = self.len();
        while lo < hi {
            let mid = lo + (hi - lo) / 2;
            if self.key(mid) < key {
                lo = mid + 1;
            } else {
                hi = mid;
            }
        }
        lo
    }

    pub fn lookup(&self, key: u64) -> Option<u64> {
        let index = self.lower_bound(key);
        (index < self.len() && self.key(index) == key)
            .then(|| word(self.bytes, 24 + index * 16))
    }

    pub fn range_indices(&self, bounds: Range<u64>) -> Range<usize> {
        let start = self.lower_bound(bounds.start);
        let end = self.lower_bound(bounds.end);
        start..end
    }

    pub fn iter_indices(&self, range: Range<usize>) -> impl Iterator<Item = Record> + '_ {
        (range.start..range.end.min(self.len())).map(|index| self.record(index))
    }

    pub fn decode(&self) -> Vec<Record> {
        (0..self.len()).map(|index| self.record(index)).collect()
    }
}

/// Encode records whose keys are already strictly increasing.
pub fn encode(records: &[Record]) -> Vec<u8> {
    let mut bytes = Vec::with_capacity(16 + records.len() * 16);
    bytes.extend_from_slice(&(records.len() as u64).to_le_bytes());
    bytes.extend_from_slice(&1u64.to_le_bytes());
    for &(key, value) in records {
        bytes.extend_from_slice(&key.to_le_bytes());
        bytes.extend_from_slice(&value.to_le_bytes());
    }
    bytes
}
