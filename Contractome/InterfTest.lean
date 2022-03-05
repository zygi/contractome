class Test1 (A : Type u) where
  t1 : A


class Test2 {W : Type u} [Test1 W] (B : Type v) where
  t2 : W -> B


structure PointedType where
  T : Type
  mkT : T

inductive PointedTypeVal {P : PointedType} where
  | mk : P.T -> PointedTypeVal

set_option pp.all true

def test {A : PointedType} := PointedTypeVal.mk A.mkT

variable {A : PointedType}

def test3 v := show PointedTypev

def test2 : PointedTypeVal :=  PointedTypeVal.mk A.mkT




-- set_option trace.Meta.synthInstance true

variable {A : Type u} [Test1 A]
variable {B : Type v} [Test2 (W:=A) B]

def toB (a: A) : B := Test2.t2 a


-- def A := 5

class StackValue (T: Type u) where

variable {Tw : Type} [StackValue Tw] [Inhabited Tw]

-- class EVMMem {κ : Type u} [MapKey κ] {ω : Type v} [Inhabited ω] [MapValue ω] (α : Type w) where
--   empty : α
--   get (m: α) (addr : κ) : ω
--   set (m: α) (addr : κ) (val : ω) : α
--   empty_get k : get empty k = default
--   set_get (m: α) k v : get (set m k v) k = v
--   set_diff_get (m: α) k k' v (h : Not (k = k')) : get (set m k v) k' = get m k'
  

class EVMStack {ω : Type u} [StackValue ω] [Inhabited ω] (α : Type v) where
  empty : α
  -- peek? (s : α) : Option UInt32
  pop? (s : α) : Option (ω × α)
  peekn? (s : α) (n : Nat) : Option ω
  setn? (s : α) (n : Nat) (v : ω) : Option α
  push (s : α) (v : ω) : α
  size (s : α) : Nat 

-- variable (M : Type) [EVMMem M]
-- variable {S : Type v} [EVMStack (ω:=Tw) S]


structure Context where
  Tw : Type u
  Tw_i : StackValue Tw
  Tw_i2 : Inhabited Tw
  
  
  S : Type v
  stackInst: EVMStack (ω := Tw) S 
  stack : S
  -- mem : M
  -- storage : M

def update (c: Context) : Context := {c with stack := EVMStack.push c.stack One.one}
