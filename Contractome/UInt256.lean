import AssertCmd

@[irreducible] def UInt256.size : Nat := 115792089237316195423570985008687907853269984665640564039457584007913129639936
-- attribute [irreducible] UInt32.size

structure UInt256 where
  val : Fin UInt256.size

def UInt256.ofNatCore (n : @& Nat) (h : LT.lt n UInt256.size) : UInt256 := {
  val := { val := n, isLt := h }
}

def UInt256.toNat (n : UInt256) : Nat := n.val.val

instance : Repr UInt256 where
  reprPrec n _ := repr n.toNat

def UInt256.decEq (a b : UInt256) : Decidable (Eq a b) :=
  match a, b with
  | ⟨n⟩, ⟨m⟩ =>
    dite (Eq n m) (fun h => isTrue (h ▸ rfl)) (fun h => isFalse (fun h' => UInt256.noConfusion h' (fun h' => absurd h' h)))

instance : DecidableEq UInt256 := UInt256.decEq

instance : Inhabited UInt256 where
  default := UInt256.ofNatCore 0 (by decide)


instance : LT UInt256 where
  lt a b := LT.lt a.val b.val

instance : LE UInt256 where
  le a b := LE.le a.val b.val

def UInt256.decLt (a b : UInt256) : Decidable (LT.lt a b) :=
  match a, b with
  | ⟨n⟩, ⟨m⟩ => inferInstanceAs (Decidable (LT.lt n m))

def UInt256.decLe (a b : UInt256) : Decidable (LE.le a b) :=
  match a, b with
  | ⟨n⟩, ⟨m⟩ => inferInstanceAs (Decidable (LE.le n m))

instance (a b : UInt256) : Decidable (LT.lt a b) := UInt256.decLt a b
instance (a b : UInt256) : Decidable (LE.le a b) := UInt256.decLe a b

instance : Ord UInt256 where
  compare x y := compareOfLessAndEq x y

#check UInt32.ofNat

def UInt256.ofNat (n : @& Nat) : UInt256 := ⟨⟨n, sorry⟩⟩
def UInt256.ofNat' (n : Nat) (h : n < UInt256.size) : UInt256 := ⟨⟨n, h⟩⟩
def UInt256.ofUInt8 (n : UInt8) : UInt256 := ⟨⟨n.val, sorry⟩⟩
abbrev Nat.toUInt256 := UInt256.ofNat
def UInt256.add (a b : UInt256) : UInt256 := ⟨a.val + b.val⟩
def UInt256.sub (a b : UInt256) : UInt256 := ⟨a.val - b.val⟩
def UInt256.mul (a b : UInt256) : UInt256 := ⟨a.val * b.val⟩
def UInt256.div (a b : UInt256) : UInt256 := ⟨a.val / b.val⟩
def UInt256.mod (a b : UInt256) : UInt256 := ⟨a.val % b.val⟩

set_option maxRecDepth 2000
def UInt256.ones : UInt256 := ⟨⟨ (2^256) - 1, by decide ⟩⟩ 
def UInt256.modn (a : UInt256) (n : @& Nat) : UInt256 := ⟨a.val % n⟩
def UInt256.land (a b : UInt256) : UInt256 := ⟨Fin.land a.val b.val⟩
def UInt256.lor (a b : UInt256) : UInt256 := ⟨Fin.lor a.val b.val⟩
def UInt256.xor (a b : UInt256) : UInt256 := ⟨Fin.xor a.val b.val⟩
def UInt256.shiftLeft (a b : UInt256) : UInt256 := ⟨a.val <<< (modn b 256).val⟩
def UInt256.shiftRight (a b : UInt256) : UInt256 := ⟨a.val >>> (modn b 256).val⟩
def UInt256.toUInt8 (a : UInt256) : UInt8 := a.toNat.toUInt8
def UInt256.toUInt16 (a : UInt256) : UInt16 := a.toNat.toUInt16
def UInt8.toUInt256 (a : UInt8) : UInt256 := a.toNat.toUInt256
def UInt16.toUInt256 (a : UInt16) : UInt256 := a.toNat.toUInt256
def UInt32.toUInt256 (a : UInt32) : UInt256 := a.toNat.toUInt256
def UInt64.toUInt256 (a : UInt64) : UInt256 := a.toNat.toUInt256

instance : OfNat UInt256 n   := ⟨UInt256.ofNat n⟩
instance : Add UInt256       := ⟨UInt256.add⟩
instance : Sub UInt256       := ⟨UInt256.sub⟩
instance : Mul UInt256       := ⟨UInt256.mul⟩
instance : Mod UInt256       := ⟨UInt256.mod⟩
instance : HMod UInt256 Nat UInt256 := ⟨UInt256.modn⟩
instance : Div UInt256       := ⟨UInt256.div⟩


-- def UInt256.bneg (a : UInt256) : UInt256 := a.xor UInt256.ones
def UInt256.complement (a:UInt256) : UInt256 := 0-(a+1)
def UInt256.sneg (a: UInt256) : UInt256 := a.complement + 1
#assert (UInt256.sneg 3) == (0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFD : UInt256)
#assert (UInt256.sneg 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFD) == (3 : UInt256)


instance : Complement UInt256 := ⟨UInt256.complement⟩
instance : AndOp UInt256     := ⟨UInt256.land⟩
instance : OrOp UInt256      := ⟨UInt256.lor⟩
instance : Xor UInt256       := ⟨UInt256.xor⟩
instance : ShiftLeft UInt256  := ⟨UInt256.shiftLeft⟩
instance : ShiftRight UInt256 := ⟨UInt256.shiftRight⟩

def UInt256.abs (a : UInt256) : UInt256 :=
  if a >>> 255 == 1 then a.sneg else a

def UInt256.sdiv (a b:UInt256) : UInt256 := 
    let a' := a.abs
    let b' := b.abs
    let r := a' / b'
    let bit : UInt256 := (a ^^^ b) >>> 255
    if bit == 1 then r.sneg else r
    
def UInt256.smod (a b:UInt256) : UInt256 := 
    let a' := a.abs
    let b' := b.abs
    let r := a' % b'
    let bit : UInt256 := a >>> 255
    if bit == 1 then r.sneg else r


@[simp]
def Nat.half_is_less (n : Nat) : (Nat.succ n) / 2 < (Nat.succ n) := sorry
  -- 
-- set_option pp.all true
def Nat.powmod_correct (a b N: Nat) : { r : Nat // r = (a.pow b) % N } := match b with
  | 0 => by cases N with | zero => exact ⟨ 1, by simp [Nat.pow, Nat.mod_zero] ⟩ 
                         | succ N => cases N with
                          | zero => exact ⟨ 0, by simp [Nat.pow]⟩ 
                          | succ N => exact ⟨ 1, by simp [Nat.pow]; rw [Nat.mod_eq_of_lt (_ : 1 < Nat.succ (Nat.succ N))]; apply Nat.succ_le_succ; apply Nat.succ_le_succ; apply Nat.zero_le ⟩ 
  | Nat.succ b => 
    if (Nat.succ b) % 2 == 0 then ⟨ powmod_correct ((a * a) % N) ((Nat.succ b) / 2) N , sorry ⟩ 
    else ⟨ (a * powmod_correct ((a * a) % N) ((Nat.succ b) / 2) N) % N , sorry ⟩ 
termination_by _ => b
decreasing_by apply Nat.half_is_less

#assert ((123 ^ 123) % 8) == (Nat.powmod_correct 123 123 8).val
#assert  (Nat.powmod_correct 2 2 8).val == ((2 ^ 2) % 8)


def Fin.pow {h : n > 0} (a b : Fin n) : Fin n :=
  let ⟨ val, prop ⟩ := Nat.powmod_correct a b n
  ⟨ val, by subst prop; exact Nat.mod_lt (Nat.pow a.val b.val) h ⟩ 

-- #eval Fin.pow ⟨ Fin.mk 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF UInt256.size


-- TODO make faster by modding intermediately
def UInt256.pow (a b:UInt256) : UInt256 := ⟨ Fin.pow (h:=by simp) a.val b.val ⟩
#eval UInt256.pow 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF

-- def UInt256.sOfInt (a: Int) := if a
def UInt256.isSpos (a: UInt256) : Bool := if (a >>> 255) == 1 then false else true
def UInt256.slt (a b: UInt256) : Bool :=
  let aS := a.isSpos
  let bS := b.isSpos
  match aS, bS with
  | true, false => false
  | false, true => true
  | _, _ => a < b

#assert (UInt256.slt (UInt256.sneg 1) 5) == true
#assert (UInt256.slt 4 5) == true
#assert (UInt256.slt 5 5) == false
#assert (UInt256.slt 6 5) == false
#assert (UInt256.slt (UInt256.sneg 1) (UInt256.sneg 1)) == false
#assert (UInt256.slt 6 (UInt256.sneg 1)) == false
#assert (UInt256.slt (UInt256.sneg 2) (UInt256.sneg 1)) == true
#assert (UInt256.slt (UInt256.sneg 1) (UInt256.sneg 2)) == false

def UInt256.sgt (a b: UInt256) : Bool := if a == b then false else !UInt256.slt a b

#print UInt64.ofNat

def UInt256.ofBytes! (b: ByteArray) : UInt256 := 
  let bs := ByteArray.mkEmpty (256 / 8)
  let destOff := (256 / 8) - b.size 
  let bs : ByteArray := ByteArray.copySlice b 0 bs destOff b.size
  -- now we can go byte by byte
  let p1 := (ByteArray.toUInt64LE! $ bs.extract 0 8).toUInt256
  let p2 := (ByteArray.toUInt64LE! $ bs.extract 8 16).toUInt256
  let p3 := (ByteArray.toUInt64LE! $ bs.extract 16 24).toUInt256
  let p4 := (ByteArray.toUInt64LE! $ bs.extract 24 32).toUInt256

  (p1 <<< 192) ||| (p2 <<< 128) ||| (p3 <<< 64) ||| p4

#assert (UInt256.ofBytes! $ ByteArray.mk $ #[0]) == (0:UInt256)
#assert (UInt256.ofBytes! $ ByteArray.mk $ #[0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 
0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 
0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 
0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 
0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 
0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 
0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 
0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 
0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 
0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 
0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 
0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 
0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 
0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 
0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 
0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff]) == UInt256.ofNat $ UInt256.size - 1
#assert (UInt256.ofBytes! $ ByteArray.mk $ #[0x80, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 
0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 
0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 
0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 
0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 
0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 
0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 
0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 
0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 
0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 
0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 
0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 
0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 
0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 
0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 
0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00]) == UInt256.ofNat $ UInt256.size / 2


def UInt256.signextend (byteNum x : UInt256) :=
  if byteNum > 31 then x else
  let bitNum := byteNum*8+7
  let mask := ((1:UInt256) <<< bitNum) - 1
  let isBitSet := (x >>> bitNum) &&& 1 == 1
  if isBitSet then x ||| (~~~ mask) else x &&& mask

#assert (UInt256.signextend 0 0xFF) == (0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF : UInt256)
#assert (UInt256.signextend 0 0x7F) == (0x7F : UInt256)


def UInt256.sar (x shiftBy : UInt256) := 
    if x.isSpos then x >>> shiftBy else
    let mask := UInt256.ones <<< (256 - shiftBy)
    (x >>> shiftBy) ||| mask

#assert (UInt256.sar 2 1) == (1 : UInt256)
#assert (UInt256.sar 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF0 4) == 
  (0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF : UInt256)
