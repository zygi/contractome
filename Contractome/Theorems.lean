import Contractome.EVM

open EVM


variable {C : Cfg} [DecidableEq C.Tw] [∀ n, OfNat C.Tw n] [Element C.Tw] [DecidableEq C.Tb] [∀ n, OfNat C.Tb n] [Element C.Tb]
variable [TakeBytes C.BAI]
variable [instBA : SByteArray C.Tw C.Tb C.BA C.BAI]
variable [EVMStack C.Tw C.S] [EVMStack (C.Tw × C.BA) C.RS] [EVMMapDefault C.Tw C.Tw C.AM] [EVMMapSeq C.Tw C.Tb C.BA C.BAI C.M]
variable [EVMMapBasic C.Tw C.BA C.BAM]
variable [Zero C.M]
variable [EVMMapDefault C.Tw C.M C.STM]
variable [Repr C.Tw] [Repr C.Tb] [Repr C.M] [Repr C.S] [Repr C.BA] [Repr C.BAM] [Repr C.AM] [Repr C.BA] [Repr C.STM] [Repr C.RS]


variable {c : Context (C:=C)}

set_option quotPrecheck false
syntax:67 term " b:: " term : term

macro_rules
  | `($a:term b:: $b:term)  => `(EVMStack.push (S:=C.S) $b $a)


-- syntax "b[" sepBy(term, ", ") "]" : term

-- macro_rules
--   | `(b[ $elems,* ]) => `(ByteArray.mk #[ $elems,* ])

-- #print simp


def p (x y : Nat) := x = y

-- example (x y : Nat) : p (x + y) (0 + y + x) := by
--   conv =>
--     whnf
--     rhs
--     rw [Nat.zero_add, Nat.add_comm]
--     trace_state
--     skip
--     done

-- abbrev optimistic_2stack_op {stackRest : C.S} {v1 v2 : C.Tw} (op : C.Tw -> C.Tw -> C.Tw) (opName : EVMM (C:=C) Unit) 
--   (hS : (c.stack = v1 b:: v2 b:: stackRest)) (post : EVMM (C:=C) α) :=
--   EVMM.runWithC (C:=C) (do opName; post) c =
--   EVMM.runWithC (C:=C) (post) {c with stack := (op v1 v2) b:: stackRest}

abbrev optimistic_2stack_op_s {stackRest : C.S} {v1 v2 : C.Tw} 
  {op : C.Tw -> C.Tw -> C.Tw} (opName : EVMM (C:=C) Unit) (hOp : opName = EVMM.mapStack2 op) 
  (hS : (c.stack = v1 b:: v2 b:: stackRest)) (post : EVMM (C:=C) α) :=
  EVMM.runWithC (C:=C) (do opName; post) c =
  EVMM.runWithC (C:=C) (post) {c with stack := (op v1 v2) b:: stackRest}

theorem optimistic_2stack_op {stackRest : C.S} {v1 v2 : C.Tw} 
  {op : C.Tw -> C.Tw -> C.Tw} (opName : EVMM (C:=C) Unit) (hOp : opName = EVMM.mapStack2 op) 
  (hS : (c.stack = v1 b:: v2 b:: stackRest)) (post : EVMM (C:=C) α) :
  EVMM.runWithC (C:=C) (do opName; post) c =
  EVMM.runWithC (C:=C) (post) {c with stack := (op v1 v2) b:: stackRest} :=
  by
      cases c
      simp only at *
      subst hS
      subst hOp
      conv =>
        simp [EVMM.runWithC, EVMM.mapStack2, EVMM.popStack]

abbrev optimistic_i01_add := optimistic_2stack_op (C:=C) (opName:=EVMM.i01_add) (op:=Element.add) (hOp := rfl)


  

theorem optimistic_add {stackRest : C.S} {v1 v2 : C.Tw} (hS : (c.stack = v1 b:: v2 b:: stackRest)) (post : EVMM (C:=C) α) :
  EVMM.runWithC (C:=C) (do EVMM.i01_add; post) c =
  EVMM.runWithC (C:=C) (post) {c with stack := (Element.add v1 v2) b:: stackRest}
  := by
    cases c
    simp only at *
    subst hS
    conv =>
      simp [EVMM.i01_add, EVMM.runWithC, EVMM.mapStack2, EVMM.popStack]
    


-- set_option trace.Debug.Meta.Tactic.simp true
theorem test {stackRest : C.S} {v : C.Tw} (hS : (c.stack = v b:: stackRest)) :
  EVMM.runWithC (C:=C) (EVMM.popStack) c = Except.ok (v, {c with stack := stackRest}) := by
  simp [EVMM.runWithC, StateT.run, ExceptT.run]
  cases c
  simp at *
  subst hS
  -- simp [EVMM.popStack]
  unfold EVMM.popStack
  -- simp
  -- simp
  conv =>
    lhs
    whnf
    simp

#eval 5

  -- simp (config := {zeta := false, beta := false, eta := false, etaStruct := false, iota := false, proj := false, decide := false, memoize := false})
  -- simp only [get]
  -- simp at *

  


-- theorem test {stackRest : C.S} {v1 v2 : C.Tw} (hS : (c.stack = v1 b:: v2 b:: stackRest)) :
--   EVMM.runWithC (C:=C) (EVMM.i01_add) tC cC c = Except.error EVMException.abstractValueError := by
--   simp [EVMM.runWithC, StateT.run, ExceptT.run, EVMM.i01_add]
--   unfold EVMM.mapStack2
--   unfold EVMM.popStack
  -- simp 
  
