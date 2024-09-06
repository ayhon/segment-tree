-- TODO: It may be easier to first implement a SegmentTree with a naive
--       BinaryTree and then have an implementation of the sort which
--       is efficient. Separating the implementation from the concept is
--       important in that it allows for easier proofs, since we need not
--       care for its details.
import Mathlib.Algebra.Group.Defs
import Batteries.Data.Vector.Basic
import Mathlib.Data.Nat.Defs 
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Algebra.Group.Basic

inductive Range
| mk(left right: Nat) -- inv: left <= right
| Empty
deriving Repr, BEq


namespace Range
  def from_ends(a b: Nat): Range := 
    if a < b then Range.mk a b 
    else Empty

  def contains(r: Range)(x: Nat): Bool := match r with
  | Empty => false
  | Range.mk left right => left <= x && x < right

  def intersect: Range -> Range -> Range
  | Empty, _ | _, Empty => Empty
  | Range.mk a1 b1, Range.mk a2 b2 =>
    Range.from_ends (a1.max a2) (b1.min b2)

  instance: OfNat Range n where
    ofNat := Range.mk n (n+1)

  def shift(n: Nat): Range -> Range
  | Range.mk a b => Range.mk (a+n) (b+n)
  | Empty => Empty
  /- instance: HAdd ℕ Range Range where -/
  /-   hAdd n -/ 
  /-   | Range.mk a b => Range.mk (a+n) (b+n) -/
  /-   | Empty => Empty -/
  /- instance(sym: HAdd ℕ Range Range): HAdd Range ℕ Range where -/
  /-   hAdd r n := sym.hAdd n r -/

end Range

namespace TreeImpl
inductive SegmentTree(α : Type)[AddMonoid α]:  Nat -> Type
| Branch {h: Nat}(val: α)(left right: SegmentTree α h): SegmentTree α (h+1)
-- inv: val = left.val + right.val
| Leaf(val : α) : SegmentTree α 0 deriving Repr

namespace SegmentTree
  variable{α: Type}[AddMonoid α]{h: Nat}

  def is_branch: SegmentTree α h -> Bool
  | Branch _ _ _ => true
  | _ => false

  def val: SegmentTree α h -> α
  | Leaf val 
  | Branch val _ _ => val

  def join(left right: SegmentTree α h): SegmentTree α (h+1) :=
    Branch (left.val + right.val) left right
      
  def range: SegmentTree α h → Range
  | _ => Range.mk 0 (2^h)

  def update{h: Nat}(i: Nat)(val: α)(self: SegmentTree α h)(offset: Nat := 0) : SegmentTree α h :=
    let range := self.range.shift offset
    if ! range.contains i then self else
    match self with
    | Leaf _ => Leaf val
    | Branch _ left right =>
      let (new_left, new_right) := if i >= 2^(h-1) + offset
        then (left,              right.update i val (offset + 2^(h-1)))
        else (left.update i val offset, right)
      new_left.join new_right

  def query{h: Nat}(r: Range)(self: SegmentTree α h)(offset: Nat := 0): α :=
    let actual_range := self.range.shift offset
    match self, r.intersect actual_range with
    | _, Range.Empty => 0
    | Leaf val, _ => val
    | Branch acc left right, inter =>
      if inter == actual_range then acc
      else (left.query inter offset) + (right.query inter (offset + 2^(h-1)))

  def left(t: SegmentTree α h): Option (SegmentTree α (h-1)) 
    :=  match t with
  | Branch _ left _ => .some left
  | _ => .none
  def right(t: SegmentTree α h): Option (SegmentTree α (h-1)) 
    :=  match t with
  | Branch _ _ right => .some right
  | _ => .none
end SegmentTree

namespace Examples
  open SegmentTree
  def small_tree: SegmentTree ℕ 2 :=
     ((Leaf 1).join (Leaf 2)).join ((Leaf 3).join (Leaf 4))

  #eval do ((<- small_tree.right).range : Option Range)
  #eval small_tree.query $ Range.mk 0 1
  #eval small_tree.query $ Range.mk 0 2
  #eval small_tree.query $ Range.mk 0 3
  #eval small_tree.query $ Range.mk 0 4
  #eval small_tree.query $ Range.mk 1 4
  #eval small_tree.query $ Range.mk 2 4
  #eval small_tree.query $ Range.mk 3 4

  def updated_small_tree : SegmentTree ℕ 2 := small_tree
    |>.update 0 5
    |>.update 1 6
    |>.update 2 7
    |>.update 3 8

  #eval updated_small_tree

  #eval updated_small_tree.query $ Range.mk 0 1
  #eval updated_small_tree.query $ Range.mk 0 2
  #eval updated_small_tree.query $ Range.mk 0 3
  #eval updated_small_tree.query $ Range.mk 0 4
  #eval updated_small_tree.query $ Range.mk 1 4
  #eval updated_small_tree.query $ Range.mk 2 4
  #eval updated_small_tree.query $ Range.mk 3 4
    

  def big_tree: SegmentTree ℕ 4 :=
    ((((Leaf 0).join (Leaf 8)).join
      ((Leaf 1).join (Leaf 9))).join
     (((Leaf 2).join (Leaf 10)).join
      ((Leaf 3).join (Leaf 11)))).join
    ((((Leaf 4).join (Leaf 12)).join
      ((Leaf 5).join (Leaf 13))).join
     (((Leaf 6).join (Leaf 14)).join
      ((Leaf 7).join (Leaf 15))))

  #eval big_tree.query $ Range.mk 0 16
  #eval big_tree.query $ Range.mk 1 15
  #eval big_tree.query $ Range.mk 2 14
  #eval big_tree.query $ Range.mk 3 13
  #eval big_tree.query $ Range.mk 4 12
  #eval big_tree.query $ Range.mk 5 11
  #eval big_tree.query $ Range.mk 6 10
  #eval big_tree.query $ Range.mk 7 9

end Examples
end TreeImpl
