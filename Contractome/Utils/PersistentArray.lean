/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
universe u v w

namespace MStd

inductive PersistentArrayNode (α : Type u) where
  | node (cs : Array (PersistentArrayNode α)) : PersistentArrayNode α
  | leaf (vs : Array α)                       : PersistentArrayNode α
  deriving Inhabited

namespace PersistentArrayNode

def isNode {α} : PersistentArrayNode α → Bool
  | node _ => true
  | leaf _ => false

end PersistentArrayNode

abbrev PersistentArray.initShift : Nat := 1
abbrev PersistentArray.branching : Nat := (2 ^ PersistentArray.initShift)

structure PersistentArray (α : Type u) where
  /- Recall that we run out of memory if we have more than `usizeSz/8` elements.
     So, we can stop adding elements at `root` after `size > usizeSz`, and
     keep growing the `tail`. This modification allow us to use `Nat` instead
     of `Nat` when traversing `root`. -/
  root    : PersistentArrayNode α := PersistentArrayNode.node (Array.mkEmpty PersistentArray.branching)
  tail    : Array α               := Array.mkEmpty PersistentArray.branching
  size    : Nat                   := 0
  shift   : Nat                 := PersistentArray.initShift
  tailOff : Nat                   := 0
  deriving Inhabited

abbrev PArray (α : Type u) := PersistentArray α

namespace PersistentArray
/- TODO: use proofs for showing that array accesses are not out of bounds.
   We can do it after we reimplement the tactic framework. -/
variable {α : Type u}
open MStd.PersistentArrayNode

def empty : PersistentArray α := {}

def isEmpty (a : PersistentArray α) : Bool := a.size == 0

def mkEmptyArray : Array α := Array.mkEmpty branching

abbrev mul2Shift (i : Nat) (shift : Nat) : Nat := i.shiftLeft shift
abbrev div2Shift (i : Nat) (shift : Nat) : Nat := i.shiftRight shift
abbrev mod2Shift (i : Nat) (shift : Nat) : Nat := i % (2 ^ shift)
abbrev mod2Shift' (i : Nat) (shift : Nat) : Nat := Nat.land i ((Nat.shiftLeft 1 shift) - 1)

-- #eval mod2Shift 10 0
-- #eval mod2Shift' 31 0


partial def getAux [Inhabited α] : PersistentArrayNode α → Nat → Nat → α
  | node cs, i, shift => getAux (cs.get! (div2Shift i shift)) (mod2Shift i shift) (shift - initShift)
  | leaf cs, i, _     => cs.get! i

def get! [Inhabited α] (t : PersistentArray α) (i : Nat) : α :=
  if i >= t.tailOff then
    t.tail.get! (i - t.tailOff)
  else
    getAux t.root (i) t.shift

def getOp [Inhabited α] (self : PersistentArray α) (idx : Nat) : α :=
  self.get! idx

partial def setAux : PersistentArrayNode α → Nat → Nat → α → PersistentArrayNode α
  | node cs, i, shift, a =>
    let j     := div2Shift i shift
    let i     := mod2Shift i shift
    let shift := shift - initShift
    node $ cs.modify j $ fun c => setAux c i shift a
  | leaf cs, i, _,     a => leaf (cs.set! i a)

def set (t : PersistentArray α) (i : Nat) (a : α) : PersistentArray α :=
  if i >= t.tailOff then
    { t with tail := t.tail.set! (i - t.tailOff) a }
  else
    { t with root := setAux t.root (i) t.shift a }

@[specialize] partial def modifyAux [Inhabited α] (f : α → α) : PersistentArrayNode α → Nat → Nat → PersistentArrayNode α
  | node cs, i, shift =>
    let j     := div2Shift i shift
    let i     := mod2Shift i shift
    let shift := shift - initShift
    node $ cs.modify j $ fun c => modifyAux f c i shift
  | leaf cs, i, _     => leaf (cs.modify i f)

@[specialize] def modify [Inhabited α] (t : PersistentArray α) (i : Nat) (f : α → α) : PersistentArray α :=
  if i >= t.tailOff then
    { t with tail := t.tail.modify (i - t.tailOff) f }
  else
    { t with root := modifyAux f t.root (i) t.shift }

def mkNewPath (shift : Nat) (a : Array α) : PersistentArrayNode α :=
  match shift with
  | 0 => leaf a 
  | Nat.succ shift =>
    node (mkEmptyArray.push (mkNewPath ((Nat.succ shift) - initShift) a))
-- termination_by _ shift _ => shift


-- theorem thmm : i > 0 -> mod2Shift i sh <= i := sorry

-- #print Nat.lt_w

-- theorem arithm1 (h: Not (a < b)) : 0 < a := by
--   have h2 : b <= a := by admit

-- #print WellFoundedRelation.rel

partial def insertNewLeaf : PersistentArrayNode α → Nat → Nat → Array α → PersistentArrayNode α
  | node cs,   i, shift, a =>
    dite (i < branching) (fun _ => node (cs.push (leaf a)))
    fun f =>
      let j     := div2Shift i shift
      let i     := mod2Shift i shift
      let shift := shift - initShift
      if j < cs.size then
         node $ cs.modify j fun c => insertNewLeaf c i shift a
      else
         node $ cs.push $ mkNewPath shift a
  | n, _, _, _ => n -- unreachable
-- termination_by _ i _ _ => i
-- decreasing_by apply thmm

def mkNewTail (t : PersistentArray α) : PersistentArray α :=
  if t.size <= (mul2Shift 1 (t.shift + initShift)) then
    { t with
      tail    := mkEmptyArray, root := insertNewLeaf t.root ((t.size - 1)) t.shift t.tail,
      tailOff := t.size }
  else
    { t with
      tail := #[],
      root := let n := mkEmptyArray.push t.root;
              node (n.push (mkNewPath t.shift t.tail)),
      shift   := t.shift + initShift,
      tailOff := t.size }

def tooBig : Nat := USize.size / 8

def push (t : PersistentArray α) (a : α) : PersistentArray α :=
  let r := { t with tail := t.tail.push a, size := t.size + 1 }
  if r.tail.size < branching || t.size >= tooBig then
    r
  else
    mkNewTail r

private def emptyArray {α : Type u} : Array (PersistentArrayNode α) :=
  Array.mkEmpty PersistentArray.branching

partial def popLeaf : PersistentArrayNode α → Option (Array α) × Array (PersistentArrayNode α)
  | n@(node cs) =>
    if h : cs.size ≠ 0 then
      let idx : Fin cs.size := ⟨cs.size - 1, by exact Nat.pred_lt h⟩
      let last := cs.get idx
      let cs'  := cs.set idx default
      match popLeaf last with
      | (none,   _)       => (none, emptyArray)
      | (some l, newLast) =>
        if newLast.size == 0 then
          let cs' := cs'.pop
          if cs'.isEmpty then (some l, emptyArray) else (some l, cs')
        else
          (some l, cs'.set (Array.size_set cs idx _ ▸ idx) (node newLast))
    else
      (none, emptyArray)
  | leaf vs   => (some vs, emptyArray)

def pop (t : PersistentArray α) : PersistentArray α :=
  if t.tail.size > 0 then
    { t with tail := t.tail.pop, size := t.size - 1 }
  else
    match popLeaf t.root with
    | (none, _) => t
    | (some last, newRoots) =>
      let last       := last.pop
      let newSize    := t.size - 1
      let newTailOff := newSize - last.size
      if newRoots.size == 1 && (newRoots.get! 0).isNode then
        { root    := newRoots.get! 0,
          shift   := t.shift - initShift,
          size    := newSize,
          tail    := last,
          tailOff := newTailOff }
      else
        { t with
          root    := node newRoots,
          size    := newSize,
          tail    := last,
          tailOff := newTailOff }

section
variable {m : Type v → Type w} [Monad m]
variable {β : Type v}

@[specialize] private partial def foldlMAux (f : β → α → m β) : PersistentArrayNode α → β → m β
  | node cs, b => cs.foldlM (fun b c => foldlMAux f c b) b
  | leaf vs, b => vs.foldlM f b

@[specialize] private partial def foldlFromMAux (f : β → α → m β) : PersistentArrayNode α → Nat → Nat → β → m β
  | node cs, i, shift, b => do
    let j    := (div2Shift i shift)
    let b ← foldlFromMAux f (cs.get! j) (mod2Shift i shift) (shift - initShift) b
    cs.foldlM (init := b) (start := j+1) fun b c => foldlMAux f c b
  | leaf vs, i, _, b => vs.foldlM (init := b) (start := i) f

@[specialize] def foldlM (t : PersistentArray α) (f : β → α → m β) (init : β) (start : Nat := 0) : m β := do
  if start == 0 then
    let b ← foldlMAux f t.root init
    t.tail.foldlM f b
  else if start >= t.tailOff then
    t.tail.foldlM (init := init) (start := start - t.tailOff) f
  else do
    let b ← foldlFromMAux f t.root (start) t.shift init
    t.tail.foldlM f b

@[specialize] private partial def foldrMAux [Monad m] (f : α → β → m β) : PersistentArrayNode α → β → m β
  | node cs, b => cs.foldrM (fun c b => foldrMAux f c b) b
  | leaf vs, b => vs.foldrM f b

@[specialize] def foldrM [Monad m] (t : PersistentArray α) (f : α → β → m β) (init : β) : m β := do
  foldrMAux f t.root (← t.tail.foldrM f init)

@[specialize]
partial def forInAux {α : Type u} {β : Type v} {m : Type v → Type w} [Monad m] [inh : Inhabited β]
    (f : α → β → m (ForInStep β)) (n : PersistentArrayNode α) (b : β) : m (ForInStep β) := do
  let mut b := b
  match n with
  | leaf vs =>
    for v in vs do
      match (← f v b) with
      | r@(ForInStep.done _) => return r
      | ForInStep.yield bNew => b := bNew
    return ForInStep.yield b
  | node cs =>
    for c in cs do
      match (← forInAux f c b) with
      | r@(ForInStep.done _) => return r
      | ForInStep.yield bNew => b := bNew
    return ForInStep.yield b

@[specialize] protected def forIn (t : PersistentArray α) (init : β) (f : α → β → m (ForInStep β)) : m β := do
  match (← forInAux (inh := ⟨init⟩) f t.root init) with
  | ForInStep.done b  => pure b
  | ForInStep.yield b =>
    let mut b := b
    for v in t.tail do
      match (← f v b) with
      | ForInStep.done r => return r
      | ForInStep.yield bNew => b := bNew
    return b

instance : ForIn m (PersistentArray α) α where
  forIn := PersistentArray.forIn

@[specialize] partial def findSomeMAux (f : α → m (Option β)) : PersistentArrayNode α → m (Option β)
  | node cs => cs.findSomeM? (fun c => findSomeMAux f c)
  | leaf vs => vs.findSomeM? f

@[specialize] def findSomeM? (t : PersistentArray α) (f : α → m (Option β)) : m (Option β) := do
  match (← findSomeMAux f t.root) with
  | none   => t.tail.findSomeM? f
  | some b => pure (some b)

@[specialize] partial def findSomeRevMAux (f : α → m (Option β)) : PersistentArrayNode α → m (Option β)
  | node cs => cs.findSomeRevM? (fun c => findSomeRevMAux f c)
  | leaf vs => vs.findSomeRevM? f

@[specialize] def findSomeRevM? (t : PersistentArray α) (f : α → m (Option β)) : m (Option β) := do
  match (← t.tail.findSomeRevM? f) with
  | none   => findSomeRevMAux f t.root
  | some b => pure (some b)

@[specialize] partial def forMAux (f : α → m PUnit) : PersistentArrayNode α → m PUnit
  | node cs => cs.forM (fun c => forMAux f c)
  | leaf vs => vs.forM f

@[specialize] def forM (t : PersistentArray α) (f : α → m PUnit) : m PUnit :=
  forMAux f t.root *> t.tail.forM f

end

@[inline] def foldl (t : PersistentArray α) (f : β → α → β) (init : β) (start : Nat := 0) : β :=
  Id.run <| t.foldlM f init start

@[inline] def foldr (t : PersistentArray α) (f : α → β → β) (init : β) : β :=
  Id.run <| t.foldrM f init

@[inline] def filter (as : PersistentArray α) (p : α → Bool) : PersistentArray α :=
  as.foldl (init := {}) fun asNew a => if p a then asNew.push a else asNew

def toArray (t : PersistentArray α) : Array α :=
  t.foldl Array.push #[]

def append (t₁ t₂ : PersistentArray α) : PersistentArray α :=
  if t₁.isEmpty then
    t₂
  else
    t₂.foldl PersistentArray.push t₁

instance : Append (PersistentArray α) := ⟨append⟩

@[inline] def findSome? {β} (t : PersistentArray α) (f : α → (Option β)) : Option β :=
  Id.run $ t.findSomeM? f

@[inline] def findSomeRev? {β} (t : PersistentArray α) (f : α → (Option β)) : Option β :=
  Id.run $ t.findSomeRevM? f

def toList (t : PersistentArray α) : List α :=
  (t.foldl (init := []) fun xs x => x :: xs).reverse

section
variable {m : Type → Type w} [Monad m]
@[specialize] partial def anyMAux (p : α → m Bool) : PersistentArrayNode α → m Bool
  | node cs => cs.anyM fun c => anyMAux p c
  | leaf vs => vs.anyM p

@[specialize] def anyM (t : PersistentArray α) (p : α → m Bool) : m Bool :=
  anyMAux p t.root <||> t.tail.anyM p

@[inline] def allM (a : PersistentArray α) (p : α → m Bool) : m Bool := do
  let b ← anyM a (fun v => do let b ← p v; pure (not b))
  pure (not b)

end

@[inline] def any (a : PersistentArray α) (p : α → Bool) : Bool :=
  Id.run $ anyM a p

@[inline] def all (a : PersistentArray α) (p : α → Bool) : Bool :=
  !any a fun v => !p v

section
variable {m : Type u → Type v} [Monad m]
variable {β : Type u}

@[specialize] partial def mapMAux (f : α → m β) : PersistentArrayNode α → m (PersistentArrayNode β)
  | node cs => node <$> cs.mapM (fun c => mapMAux f c)
  | leaf vs => leaf <$> vs.mapM f

@[specialize] def mapM (f : α → m β) (t : PersistentArray α) : m (PersistentArray β) := do
  let root ← mapMAux f t.root
  let tail ← t.tail.mapM f
  pure { t with tail := tail, root := root }

end

@[inline] def map {β} (f : α → β) (t : PersistentArray α) : PersistentArray β :=
  Id.run $ t.mapM f

structure Stats where
  numNodes : Nat
  depth : Nat
  tailSize : Nat

partial def collectStats : PersistentArrayNode α → Stats → Nat → Stats
  | node cs, s, d =>
    cs.foldl (fun s c => collectStats c s (d+1))
      { s with
        numNodes := s.numNodes + 1,
        depth    := Nat.max d s.depth }
  | leaf vs, s, d => { s with numNodes := s.numNodes + 1, depth := Nat.max d s.depth }

def stats (r : PersistentArray α) : Stats :=
  collectStats r.root { numNodes := 0, depth := 0, tailSize := r.tail.size } 0

def Stats.toString (s : Stats) : String :=
  s!"\{nodes := {s.numNodes}, depth := {s.depth}, tail size := {s.tailSize}}"

instance : ToString Stats := ⟨Stats.toString⟩

end PersistentArray

def mkPersistentArray {α : Type u} (n : Nat) (v : α) : PArray α :=
  n.fold (init := PersistentArray.empty) fun i p => p.push v

@[inline] def mkPArray {α : Type u} (n : Nat) (v : α) : PArray α :=
  mkPersistentArray n v

end MStd

-- open Std (PersistentArray PersistentArray.empty)

-- def List.toPersistentArrayAux {α : Type u} : List α → PersistentArray α → PersistentArray α
--   | [],    t => t
--   | x::xs, t => toPersistentArrayAux xs (t.push x)

-- def List.toPersistentArray {α : Type u} (xs : List α) : PersistentArray α :=
--   xs.toPersistentArrayAux {}

-- def Array.toPersistentArray {α : Type u} (xs : Array α) : PersistentArray α :=
--   xs.foldl (init := PersistentArray.empty) fun p x => p.push x

-- @[inline] def Array.toPArray {α : Type u} (xs : Array α) : PersistentArray α :=
--   xs.toPersistentArray