use vstd::prelude::*;

verus! {

pub open spec fn sorted(keys: Seq<u64>) -> bool {
    forall |i: int, j: int| 0 <= i <= j < keys.len() ==> keys[i] <= keys[j]
}

pub open spec fn partition(keys: Seq<u64>, target: u64, boundary: int) -> bool {
    0 <= boundary <= keys.len()
    && (forall |i: int| 0 <= i < boundary ==> keys[i] < target)
    && (forall |i: int| boundary <= i < keys.len() ==> keys[i] >= target)
}

pub fn lower_bound(keys: &[u64], target: u64) -> (boundary: usize)
    requires sorted(keys@),
    ensures partition(keys@, target, boundary as int),
{
    let mut lo = 0;
    let mut hi = keys.len();
    while lo < hi
        invariant
            sorted(keys@),
            lo <= hi <= keys.len(),
            forall |i: int| 0 <= i < lo ==> keys@[i] < target,
            forall |i: int| hi <= i < keys.len() ==> keys@[i] >= target,
        decreases hi - lo,
    {
        let mid = lo + (hi - lo) / 2;
        if keys[mid] < target {
            assert forall |i: int| 0 <= i < mid + 1 implies keys@[i] < target by {
                assert(keys@[i] <= keys@[mid as int]);
            }
            lo = mid + 1;
        } else {
            assert forall |i: int| mid <= i < keys.len() implies keys@[i] >= target by {
                assert(keys@[mid as int] <= keys@[i]);
            }
            hi = mid;
        }
    }
    lo
}

pub fn find(keys: &[u64], target: u64) -> (result: Option<usize>)
    requires sorted(keys@),
    ensures
        match result {
            Some(i) => i < keys.len() && keys@[i as int] == target,
            None => forall |i: int| 0 <= i < keys.len() ==> keys@[i] != target,
        },
{
    let index = lower_bound(keys, target);
    if index < keys.len() && keys[index] == target {
        Some(index)
    } else {
        assert forall |i: int| 0 <= i < keys.len() implies keys@[i] != target by {
            if i >= index && index < keys.len() {
                assert(keys@[index as int] <= keys@[i]);
            }
        }
        None
    }
}

pub fn range_indices(keys: &[u64], start: u64, end: u64) -> (bounds: (usize, usize))
    requires sorted(keys@),
    ensures
        bounds.0 <= keys.len(),
        bounds.1 <= keys.len(),
        forall |i: int| 0 <= i < keys.len() ==>
            (bounds.0 <= i < bounds.1 <==> start <= #[trigger] keys@[i] < end),
{
    (lower_bound(keys, start), lower_bound(keys, end))
}

}

fn main() {}
