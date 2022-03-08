import Contractome.Interfaces
import Contractome.UInt256
import Contractome.Utils.RBMap2
import Std.Data.Stack

import Contractome.Instances.Element
import Contractome.Instances.SByteArray


open MStd (RBMap mkRBMap)

namespace EVM
-- instance : EVMMapBasic UInt256 UInt8 (RBMap UInt256 UInt8 Ord.compare) where
--   empty := mkRBMap _ _ _
--   get? m addr := m.find? addr
--   set m addr val := m.insert addr val

def idxMap (n : UInt256) := n / 32
def getGapBits (n : UInt256) : UInt256 := (n % 32) * 8

abbrev CondensedMap := RBMap UInt256 UInt256 Ord.compare

private def get? (m : CondensedMap) (addr: UInt256) : Option UInt8 :=
    match m.find? $ (idxMap addr) with
    | Option.none => none
    | Option.some val => Option.some $ UInt256.toUInt8 $ (val <<< (addr % 32)) >>> (256 - 8 : UInt256) 

instance : EVMMapBasic UInt256 UInt8 (CondensedMap) where
  empty := mkRBMap _ _ _
  get? m addr := get? m addr

  set m addr val :=
    let r := m.findD (idxMap addr) 0
    let r := r ||| ((UInt256.ofUInt8 val) <<< getGapBits addr)
    m.insert (idxMap addr) r

instance : EVMMapDefault UInt256 UInt8 (CondensedMap) where
  get m addr := (get? m addr).getD 0
  
private def get32 (m: CondensedMap) (addr: UInt256) : UInt256 :=
  if addr % 32 == 0 then m.findD (idxMap addr) 0 else
    let fst := m.findD (idxMap addr) 0
    let snd := m.findD (idxMap $ addr + 32) 0
    let gap := getGapBits addr
    let p1 := fst <<< gap
    let p2 := snd >>> (256 - gap)
    p1 ||| p2

private def set32 (m: CondensedMap) (addr: UInt256) (val : UInt256)  := Id.run do
    if addr % 32 == 0 then m.insert (idxMap addr) val else
      let fst := m.findD (idxMap addr) 0
      let snd := m.findD (idxMap $ addr + 32) 0

      let gap := getGapBits addr
      let p1 := val >>> gap
      let p2 := val <<< (256 - gap)

      let ones := UInt256.ones
      let p1' := (fst >>> (256 - gap)) <<< (256 - gap)
      let p2' := (snd <<< gap) >>> gap

      (m.insert (idxMap addr) (p1 ||| p1')).insert (idxMap $ addr + 32) (p2 ||| p2')

instance : EVMMap UInt256 UInt8 (CondensedMap) where
  get32 := get32
  set32 := set32

  maxKey m := 0

  empty_get a := by rfl
  set_get a b c := sorry
  set_diff_get a b c d e:= sorry


def concatL (l1 l2: List α) := 
  let rec aux (l1 l2: List α) : List α := match l1 with
  | List.cons l l1 => aux l1 $ List.cons l l2
  | List.nil => l2 
  aux l1.reverse l2

#assert (concatL [1, 2] [3, 4]) == [1, 2, 3, 4]

private def padL (ls : List α) (v : α) (n : Nat) := 
  let sz := ls.length
  let rec aux n ls := match n with
  | Nat.zero => ls
  | Nat.succ n => aux n (List.cons v ls)

  aux (n - sz) ls

#assert (padL [1, 2, 3] 0 0) == ([1, 2, 3])
#assert (padL [1, 2, 3] 0 3) == ([1, 2, 3])
#assert (padL [1, 2, 3] 0 4) == ([0, 1, 2, 3])


private def padR (ls : List α) (v : α) (n : Nat) := 
  let sz := ls.length
  let rec aux n ls := match n with
  | Nat.zero => ls
  | Nat.succ n => aux n (List.cons v ls)

  concatL ls (aux (n - sz) [])

#assert (padR [1, 2, 3] 0 3) == ([1, 2, 3])
#assert (padR [1, 2, 3] 0 4) == ([1, 2, 3, 0])

-- instance [Inhabited α] : Inhabited (Id α) := ⟨default⟩ 
instance : Inhabited (RBMap α β comp) := ⟨ RBMap.empty ⟩

#print "ASdf"

instance [SByteArray UInt256 UInt8 (List UInt8) (List UInt8)]:
  EVMMapSeq UInt256 UInt8 (CondensedMap) (BA := (List UInt8)) (BAI := (List UInt8)) where
  getRange m start length := Id.run do
    let mut r := List.nil
    if length == 0 then return r
    let nl := (length.toNat - 1) / 32
    for (i:Nat) in [0:nl+1] do
      r := concatL (get32 m (start + (32 * UInt256.ofNat i))).toBytesL.reverse r
    r.reverse.take length.toNat

  setRange origM start length content := Id.run do
    -- assert! (length <= SByteArray.size UInt8 (List UInt8) content)
    let mut m := origM
    if length == 0 then return m
    let nl := (length.toNat - 1) / 32
    let mut cont := content
    for (i:Nat) in [0:nl+1] do
      m := set32 m (start + (32 * UInt256.ofNat i)) $ UInt256.ofBytesL! $ padR (cont.take 32) 0 32
      cont := cont.drop 32
    m


namespace Test
  def m := mkRBMap UInt256 UInt256 Ord.compare
  #eval EVMMapBasic.set (K:=UInt256) (V:=UInt8) m 0 0xff
  #eval EVMMapBasic.set (K:=UInt256) (V:=UInt8) m 1 0xff

  -- def mof (args: List (UInt256 × UInt256)) : CondensedMap := Std.rbmapOf args _
  def mof (args: List (UInt256 × UInt256)) := args

  #assert (EVMMapBasic.set (K:=UInt256) (V:=UInt8) m 33 0xff).toList == (mof [(1, 0xff00)])
  #assert (EVMMapBasic.set (K:=UInt256) (V:=UInt8) m 63 0xff).toList == (mof [(1, UInt256.ones <<< 248)])
  #assert (EVMMapBasic.set (K:=UInt256) (V:=UInt8) m 64 0xff).toList == (mof [(2, 0xff)])

  #assert (EVMMap.set32 (K:=UInt256) (V:=UInt8) m 0 0xff).toList == (mof [(0, 0xff)])
  #assert (EVMMap.set32 (K:=UInt256) (V:=UInt8) m 32 0xff).toList == (mof [(1, 0xff)])
  #assert (EVMMap.set32 (K:=UInt256) (V:=UInt8) m 1 0xff).toList == (mof [(0, 0), (1, UInt256.ones <<< 248)])
  #assert (EVMMap.set32 (K:=UInt256) (V:=UInt8) m 31 0xff).toList == (mof [(0, 0), (1, 0xff00)])

  def withData := EVMMap.set32 (K:=UInt256) (V:=UInt8) m 2 0xffff
  def withData2 := EVMMap.set32 (K:=UInt256) (V:=UInt8) withData 1 0xcccc
  #eval withData2
  #eval withData2
  #assert (EVMMap.get32 (K:=UInt256) (V:=UInt8) withData 0) == (0:UInt256)
  #assert (EVMMap.get32 (K:=UInt256) (V:=UInt8) withData 2) == (0xffff:UInt256)
  #assert (EVMMap.get32 (K:=UInt256) (V:=UInt8) withData 1) == (0xff:UInt256)
  #assert (EVMMap.get32 (K:=UInt256) (V:=UInt8) withData 32) == (UInt256.ones <<< 240)

  #assert (EVMMap.get32 (K:=UInt256) (V:=UInt8) withData2 0) == (0xcc : UInt256)
  #assert (EVMMap.get32 (K:=UInt256) (V:=UInt8) withData2 1) == (0xcccc : UInt256)
  #assert (EVMMap.get32 (K:=UInt256) (V:=UInt8) withData2 2) == (0xccccff : UInt256)
  #assert (EVMMap.get32 (K:=UInt256) (V:=UInt8) withData2 3) == (0xccccff00 : UInt256)

  abbrev gr := EVMMapSeq.getRange (BA:=List UInt8) (K:=UInt256) (V:=UInt8) (BAI:=List UInt8) (M:=RBMap UInt256 UInt256 compare)
  abbrev sr := EVMMapSeq.setRange (BA:=List UInt8) (K:=UInt256) (V:=UInt8) (BAI:=List UInt8) (M:=RBMap UInt256 UInt256 compare)

  #eval gr withData2 3 32

  #assert (gr withData2 3 32) == (0xccccff00 : UInt256).toBytesL
  #assert (gr withData2 3 30) == ((0xcccc : UInt256).toBytesL.drop 2)
  #assert (gr withData2 3 34) == (concatL [0, 0] (0xccccff000000 : UInt256).toBytesL)


  def withData3 := sr withData2 1 3 [1, 2, 3]
  #assert (gr withData3 1 1) == ([0x01] : List UInt8)
  #assert (gr withData3 1 5) == ([0x01, 0x02, 0x03, 0, 0] : List UInt8)

  def withData4 := sr m 30 34 (concatL [1, 2] UInt256.ones.toBytesL)
  #eval withData4
  #assert (gr withData4 0 1) == ([0x00] : List UInt8)

  #assert (gr withData4 31 1) == ([0x02] : List UInt8)
  #assert (gr withData4 0 64) == (concatL (0x0102 : UInt256).toBytesL UInt256.ones.toBytesL)
  #assert (gr withData4 30 34) == (concatL [1, 2] UInt256.ones.toBytesL)
end Test

end EVM