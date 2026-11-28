import Std

namespace SortedRun

/-- The cursor belongs to one immutable run. A successful pull returns the
first remaining row and a cursor for its tail. An empty suffix returns EOF. -/
abbrev Pull (m : Type → Type) (cursor row : Type) :=
  cursor → m (Option (row × cursor))

/-- A buffered row owns the cursor immediately after that row. -/
inductive Front (cursor row : Type) where
  | unread (cursor : cursor)
  | buffered (item : Option (row × cursor))

structure Frontier (left right row : Type) where
  newer : Front left row
  older : Front right row

def Frontier.start (newer : left) (older : right) : Frontier left right row :=
  ⟨.unread newer, .unread older⟩

/-- Read and update the frontier in the consumer's effect. -/
structure Slot (m : Type → Type) (α : Type) where
  get : m α
  set : α → m Unit

def Front.fill [Monad m] (pull : Pull m cursor row) :
    Front cursor row → m (Option (row × cursor))
  | .unread cursor => pull cursor
  | .buffered item => pure item

/-- Only this decision inspects keys. A tie consumes both heads and emits
the entire newer row. -/
def choose [LT key] [DecidableLT key] (keyOf : row → key)
    (newer : Option (row × left)) (older : Option (row × right)) :
    Option row × Frontier left right row :=
  match newer, older with
  | none, none => (none, ⟨.buffered none, .buffered none⟩)
  | some (a, next), none => (some a, ⟨.unread next, .buffered none⟩)
  | none, some (b, next) => (some b, ⟨.buffered none, .unread next⟩)
  | some (a, nextA), some (b, nextB) =>
    if keyOf a < keyOf b then (some a, ⟨.unread nextA, .buffered older⟩)
    else if keyOf b < keyOf a then (some b, ⟨.buffered newer, .unread nextB⟩)
    else (some a, ⟨.unread nextA, .unread nextB⟩)

/-- One callback for a streaming consumer. Fill only missing heads, with
the newer fill committed before probing the older run. A failed pull
returns through the monad before any comparison or subsequent probe. -/
@[inline] def next [Monad m] [LT key] [DecidableLT key] (keyOf : row → key)
    (readNewer : Pull m left row) (readOlder : Pull m right row)
    (slot : Slot m (Frontier left right row)) : m (Option row) := do
  let before ← slot.get
  let newer ← before.newer.fill readNewer
  slot.set { before with newer := .buffered newer }
  let older ← before.older.fill readOlder
  let (item, after) := choose keyOf newer older
  slot.set after
  return item

end SortedRun
