import Lean
import Lean.Elab.Command
import Lean.Elab.Tactic.Basic
import Mathlib.Lean.Expr
import Lean.Meta
import AssertCmd

open Lean Elab Elab.Tactic

-- #print mkIdent

-- #reduce Parser.Term.quot

def doWork : Command.CommandElabM Unit := do
  for i in [0:256] do    -- stxs := stxs.push $  
    -- let name := Syntax.mkNameLit s!"name{i}"
    Command.elabCommand (← `(theorem $(mkIdent s!"number{i}_lt") : $(quote i) < 256 := by simp ))
    Command.elabCommand (← `(def $(mkIdent s!"number{i}") : UInt8 := ⟨ $(quote i), $(mkIdent s!"number{i}_lt") ⟩ ))
    -- Command.elabCommand (← `(theorem $(quote name) : $i < 256 := by simp))
    pure ()

  let mut matchArms : Array Syntax := #[]
  for i in [0:256] do    -- stxs := stxs.push $  
      -- let name := Syntax.mkNameLit s!"name{i}"
      matchArms := matchArms.push (← `(Parser.Term.matchAltExpr| | $(quote i) => $(mkIdent s!"number{i}")))
      -- Command.elabCommand (← `(theorem $(quote name) : $i < 256 := by simp))
      pure ()

  matchArms := matchArms.push (← `(Parser.Term.matchAltExpr| | n => ⟨ 0, by simp⟩ ))
  
  let dfn ← `(def $(mkIdent "fofNat") (n : Nat) : UInt8 := match n % 256 with $matchArms:matchAlt*)
  Command.elabCommand dfn

-- constant a : 4 < 5 := by simp

--   pure ()

syntax (name := genTest) "gen_uint_helper_theorems" : command
@[commandElab genTest]
unsafe def elabAssert : Command.CommandElab
  | _ => do doWork

-- set_option maxHeartbeats 500000
-- gen_uint_helper_theorems

-- def fofNat : Nat -> UInt8
-- | n => UInt8.ofNat n

-- -- opaque mod_lt_o (x : Nat) {y : Nat} : y > 0 → x % y < y := Nat.mod_lt
-- @[irreducible] 
-- def tofNat (a : Nat) : UInt8 :=
--   ⟨a % 256, let x := Nat.mod_lt a (Nat.zero_lt_succ 255); x⟩


-- local instance : OfNat UInt8 n where
--   ofNat := match n with 
--   | 0 => ⟨ 0, name0⟩ 
--   | 1 => ⟨ 1, name1⟩ 
--   | _ => UInt8.ofNat n


-- set_option maxRecDepth 10000
-- set_option pp.all true

@[inline]
def hexChar (c: Char): Option Nat :=
  if '0' ≤ c ∧ c ≤ '9' then
    some $ c.val.toNat - '0'.val.toNat
  else if 'a' ≤ c ∧ c ≤ 'f' then
    some $ c.val.toNat - 'a'.val.toNat + 10
  else if 'A' ≤ c ∧ c ≤ 'F' then
    some $ c.val.toNat - 'A'.val.toNat + 10
  else
    none

def hexToByteArray(s: String): Option ByteArray := Id.run do
  if s.length % 2 != 0 then return none
  let mut res := ByteArray.mkEmpty $ s.length / 2
  for i in [:((s.length)/2)] do
    let v1 := hexChar (s[2*i])
    let v2 := hexChar (s[2*i+1])
    match (v1, v2) with 
    | (some v1, some v2) => res := res.push $ UInt8.ofNat ((16 * v1) + v2)
    | _ => return none
  return res

def hexToByteArray!(s: String): ByteArray := Id.run do
  if s.length % 2 != 0 then return ByteArray.empty
  let mut res := ByteArray.mkEmpty $ s.length / 2
  for i in [:((s.length)/2)] do
    let v1 := match hexChar (s[2*i]) with | Option.none => panic! "Bad hex" | Option.some x => x
    let v2 := match hexChar (s[2*i+1]) with | Option.none => panic! "Bad hex" | Option.some x => x
    let val := (16 * v1) + v2
    -- res := res.push $ UInt8.ofNat val
    res := res.push $ ⟨ val, sorry ⟩ 
  return res

def hexToByteList!(s: String): List UInt8 := Id.run do
  if s.length % 2 != 0 then return []
  let mut res : List UInt8 := []
  for i in [:((s.length)/2)] do
    let v1 := match hexChar (s[2*i]) with | Option.none => panic! "Bad hex" | Option.some x => x
    let v2 := match hexChar (s[2*i+1]) with | Option.none => panic! "Bad hex" | Option.some x => x
    let val := (16 * v1) + v2
    -- res := res.push $ UInt8.ofNat val
    res := List.cons ⟨ val, sorry ⟩ res
  return res.reverse

def ByteArray.mkZeros (n:Nat) := Id.run do
  let mut b := ByteArray.mkEmpty n
  for i in [0:n] do
    b := b.push 0
  b


def byteArrayToHex(b: ByteArray) : String := 
  let parts := b.data.map (fun x => String.singleton (Nat.digitChar (x.toNat / 16)) ++ String.singleton (Nat.digitChar (x.toNat % 16)))
  String.join parts.toList


syntax "b[" sepBy(term, ", ") "]" : term
macro_rules
  | `(b[ $elems,* ]) => `(ByteArray.mk #[ $elems,* ])


-- syntax (name := redComp) "#redComp" : command
@[commandParser] def redComp := leading_parser "#redComp " >> Lean.Parser.termParser

@[commandElab redComp]
def elabRedComp : Command.CommandElab
  | `(#redComp%$tk $term) => withoutModifyingEnv <| Command.runTermElabM (some `_check) fun _ => do
    let e ← Term.elabTerm term none
    Term.synthesizeSyntheticMVarsNoPostponing
    let (e, _) ← Term.levelMVarToParam (← Meta.instantiateMVars e)
    -- TODO: add options or notation for setting the following parameters
    withTheReader Core.Context (fun ctx => { ctx with options := ctx.options.setBool `smartUnfolding true }) do
      let e ← Meta.withTransparency (mode := Meta.TransparencyMode.default) <| Meta.reduce e (skipProofs := true) (skipTypes := false)
      logInfoAt tk e
  | _ => throwUnsupportedSyntax

@[commandParser] def red' := leading_parser "#reduce' " >> Lean.Parser.termParser
@[commandElab red']
def elabRed' : Command.CommandElab
  | `(#reduce'%$tk $term) => withoutModifyingEnv <| Command.runTermElabM (some `_check) fun _ => do
    let e ← Term.elabTerm term none
    Term.synthesizeSyntheticMVarsNoPostponing
    let (e, _) ← Term.levelMVarToParam (← Meta.instantiateMVars e)
    -- TODO: add options or notation for setting the following parameters
    withTheReader Core.Context (fun ctx => { ctx with options := ctx.options.setBool `smartUnfolding true }) do
      let e ← Meta.withTransparency (mode := Meta.TransparencyMode.default) <| Meta.reduce e (skipProofs := false) (skipTypes := false)
      logInfoAt tk e
  | _ => throwUnsupportedSyntax


@[commandParser] def redDontPrint := leading_parser "#redDontPrint " >> Lean.Parser.termParser
@[commandElab redDontPrint]
def elabRedDontPrint : Command.CommandElab
  | `(#redDontPrint%$tk $term) => withoutModifyingEnv <| Command.runTermElabM (some `_check) fun _ => do
    let e ← Term.elabTerm term none
    Term.synthesizeSyntheticMVarsNoPostponing
    let (e, _) ← Term.levelMVarToParam (← Meta.instantiateMVars e)
    -- TODO: add options or notation for setting the following parameters
    withTheReader Core.Context (fun ctx => { ctx with options := ctx.options.setBool `smartUnfolding true }) do
      let e ← Meta.withTransparency (mode := Meta.TransparencyMode.default) <| Meta.reduce e (skipProofs := false) (skipTypes := false)
      -- logInfoAt tk e
  | _ => throwUnsupportedSyntax

-- #print Lean.Parser.Command.reduce
-- #reduce (⟨5, sorry⟩ : UInt8)
-- #reduce (5 : UInt8)

-- #reduce String.foldr

-- let rec loop (i : Pos) (a : α) :=
--     if i == stopPos then a
--     else loop (s.next i) (f a (s.get i))
--   loop i a

theorem termination (t: String) (i: String.Pos) : String.length t - String.next t i < String.length t - i := by admit
  -- simp [Nat.le_of_add_le_add_right, Nat.lt_of_succ_le]
  -- simp [String.length, String.next, String.get, String.csize]

@[specialize] private def loop [Monad m] (d: σ) (t: String) (i : String.Pos) (f : Char → σ → m (ForInStep σ)) : m σ := do
    if i == t.length then pure d else
    match (← f (t.get i) d) with
      | ForInStep.done d  => pure d
      | ForInStep.yield d => loop d t (t.next i) f
termination_by _ t i _ => (t.length - i)
decreasing_by apply termination

@[inline] private def forIn [Monad m] (t : String) (init : σ) (f : Char → σ → m (ForInStep σ)) : m σ :=
  loop init t 0 f

instance : ForIn m String Char where
  forIn := forIn


-- #redComp fofNat 5
def hexToByteArray'(s: String): Option ByteArray := Id.run do
  if s.length % 2 != 0 then return none
  let mut res := ByteArray.mkEmpty $ s.length / 2
  let mut mem : Option UInt8 := Option.none
  -- s.foldl 
  for c in s do
    let Option.some r := hexChar c | return none    
    (res, mem) := match mem with 
    | none => (res, Option.some ⟨ r , sorry ⟩ )
    | some r2 => (res.push $ (16 * (⟨ r , sorry ⟩ : UInt8) ) + r2, Option.none)
    pure ()
  return res

def hexToByteArray!'_aux (l: List Char) (r: ByteArray) : ByteArray := match l with
| List.cons v1 (List.cons v2 l) => match hexChar v1 with
  | none => panic! "Asdf"
  | some v1 => match hexChar v2 with
    | none => panic! "asdf"
    | some v2 =>
      (hexToByteArray!'_aux l r).push ⟨ 16 * v1 + v2 , sorry ⟩
| List.nil => r
| _ => panic! "wrong size"

def hexToByteArray!' (s: String) :=
  let d := hexToByteArray!'_aux s.data ByteArray.empty
  ByteArray.mk (d.data.reverse)


def hexToByteList!'_aux (l: List Char) (r: List UInt8) : List UInt8 := match l with
| List.cons v1 (List.cons v2 l) => match hexChar v1 with
  | none => panic! "Asdf"
  | some v1 => match hexChar v2 with
    | none => panic! "asdf"
    | some v2 =>
      List.cons ⟨ 16 * v1 + v2 , sorry ⟩ (hexToByteList!'_aux l r)
| List.nil => r
| _ => panic! "wrong size"

def hexToByteList!' (s: String) :=
  let d := hexToByteList!'_aux s.data []
  d


#assert (hexToByteList! "deadbeef00") == (hexToByteList!' "deadbeef00")
-- def hexToByteArray''(s: String): Option ByteArray := 
--   let fn (st : (Option UInt8 × ))
-- s.foldl

-- #print hexToByteArray'

-- local instance : OfNat UInt8 n where
--   -- ofNat := fofNat n
--   ofNat := ⟨ n % 256, sorry ⟩


-- set_option pp.all true
-- #reduce (5: UInt8)


-- -- private def throwFailedToEval (e : Expr) : MetaM α :=
-- --   throwError "reduceEval: failed to evaluate argument{indentExpr e}"
    
-- -- instance : Meta.ReduceEval UInt8 where
-- --   reduceEval e := do
-- --     let e ← Meta.whnf e
-- --     let Expr.const c .. ← pure e.getAppFn | throwFailedToEval e
-- --     let nargs := e.getAppNumArgs
-- --     if      c == `UInt8.mk && nargs == 0 then pure none
-- --     else if c == `Option.some && nargs == 1 then some <$> reduceEval e.appArg!
-- --     else throwFailedToEval e

-- #reduce fofNat 5

-- def basicInput := hexToByteArray "604260005260206000F3"
-- -- -- #reduce (22 : UInt8)
-- -- -- set_option maxHeartbeats 200000
-- -- -- #reduce basicInput

-- -- -- #reduce basicInput

-- -- def basicSolcInput := hexToByteArray! "6080604052348015600f57600080fd5b5060405160e338038060e38339818101604052810190602d9190604c565b80600081905550506097565b6000815190506046816083565b92915050565b600060208284031215605f57605e607e565b5b6000606b848285016039565b91505092915050565b6000819050919050565b600080fd5b608a816074565b8114609457600080fd5b50565b603f8060a46000396000f3fe6080604052600080fdfea26469706673582212209c130309b4505633bae9459145bea0f6138a99c38947f11384f39beca020bc9a64736f6c63430008070033"



-- def basicInlined : ByteArray := {data := #[96, 128, 96, 64, 82, 52, 128, 21, 96, 15, 87, 96, 0, 128, 253, 91, 80, 96, 64, 81, 96,
-- 227, 56, 3, 128, 96, 227, 131, 57, 129, 129, 1, 96, 64, 82, 129, 1, 144,
-- 96, 45, 145, 144, 96, 76, 86, 91, 128, 96, 0, 129, 144, 85, 80, 80, 96, 151, 86, 91, 96, 0, 129, 81, 144, 80, 96, 70, 129, 96,
-- 131, 86, 91, 146, 145, 80, 80, 86, 91, 96, 0, 96, 32, 130, 132, 3, 18, 21, 96, 95, 87, 96, 94, 96, 126, 86, 91, 91, 96, 0, 96,
-- 107, 132, 130, 133, 1, 96, 57, 86, 91, 145, 80, 80, 146, 145, 80, 80, 86, 91, 96, 0, 129, 144, 80, 145, 144, 80, 86, 91, 96]}
-- --, 0, 128, 253, 91, 96, 138, 129, 96, 116, 86, 91, 129, 20, 96, 148, 87, 96, 0, 128, 253, 91, 80, 86, 91, 96, 63, 128, 96, 164, 96, 0, 57, 96, 0, 243, 254, 96, 128, 96, 64, 82, 96, 0, 128, 253, 254, 162, 100, 105, 112, 102, 115, 88, 34, 18, 32, 156, 19, 3, 9, 180, 80, 86, 51, 186, 233, 69, 145, 69, 190, 160, 246, 19, 138, 153, 195, 137, 71, 241, 19, 132, 243, 155, 236, 160, 32, 188, 154, 100, 115, 111, 108, 99, 67, 0, 8, 7, 0, 51]}

-- -- set_option pp.all true
-- -- #eval basicInlined
-- set_option maxRecDepth 10000

-- #reduce basicInlined[100]

-- #reduce (20 : UInt8)
-- #reduce {data := #[96, 128, 96, 64, 82, 52, 128, 21, 96, 15] : ByteArray}

-- #redComp hexToByteArray!' "aabbccccdd"
-- #redComp basicInput
-- #redComp (1 : UInt8)

