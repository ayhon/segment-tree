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
open Batteries.Vector


/--
A SegmentTree is a balanced binary tree which holds
elements of some Monoid α on its leaves. The root of
a SegmentTree holds the aggregation of the elements
of its leaves, and the left and right subtrees of 
each branch are SegmentTrees themselves.

A SegmentTree of an array of n elements is represented
by an array of n elements, where the element at position
0 is left unused, the element at position 1 is the root
of the SegmentTree, and for each node i, the node at 
position 2*i is its left child and the node at position
2*i+1 is its right child.

In particular, this means that the i-th element of the
original array is in the n+i position in the SegmentTree's
array. (theorem)
Furthermore, if the original array has length n, then the
SegmentTree takes 2*n the same space. (theorem) This is
actually only true if n is a power of 2, since otherwise
the array is filled with the neutral element to fill up
to the nearest power of two.
- The idea is that, at each level of the 

-/
structure SegmentTree(α : Type)(k: Nat)[Monoid α] where
  v: Batteries.Vector α (2^k)
deriving Repr

namespace SegmentTree
  inductive Range
  | mk(left right: Nat)(inv: left <= right): Range
  | Empty : Range
  deriving Repr

  namespace Range 
    def contains: Range → Nat → Bool
    | Empty, _  => false
    | .mk l r _, x => l <= x && x <= r

    @[simp]
    def from_ends(l r: Nat): Range := 
      if h: l <= r 
      then .mk l r h 
      else .Empty

    def intersect: Range → Range → Range
    | Empty, _ 
    | _, Empty => Empty
    | .mk la ra _, .mk lb rb _ => 
      let l := max la lb
      let r := min ra rb
      Range.from_ends l r

    #eval (Range.mk 3 7 (by simp)).intersect (Range.mk 2 4 (by simp))

    def size: Range -> Nat
    | Empty => 0
    | .mk l r _ => r - l + 1

    @[simp] 
    def split: Range -> Range × Range
    | Empty => (Empty, Empty)
    | .mk l r _ =>
      let mid := (l + r) / 2
      let lhs := Range.from_ends l mid
      let rhs := Range.from_ends (mid+1) r
      (lhs, rhs)

    def only_if(p q: Prop): Prop := q -> p
    instance : Trans only_if only_if only_if where
      trans := by
        intros _ _ _ qp rq
        exact qp ∘ rq

    lemma lower_le_midpoint{a b: Nat}(a_le_b: a ≤ b): a ≤ (a+b)/2 := by
      calc
        a ≤ (2*a)/2 := by
          rw [Nat.mul_div_cancel_left]
          · simp
        _ ≤ (a+a)/2 := by  
          rw [Nat.two_mul]
        _ ≤ (a+b)/2 := by
          apply Nat.div_le_div_right
          apply Nat.add_le_add_left
          exact a_le_b

    lemma midpoint_le_upper{a b: Nat}(a_le_b: a ≤ b): (a+b)/2 ≤ b := by
      calc
        (a+b)/2 ≤ (b + b)/2 := by
          apply Nat.div_le_div_right
          apply Nat.add_le_add_right
          exact a_le_b
        _ ≤ (2*b)/2 := by
          rw [Nat.two_mul]
        _ ≤ b := by  
          rw [Nat.mul_div_cancel_left]
          · simp

    theorem split_preserves_size(r lhs rhs: Range)
      (rel: r.split = (lhs, rhs)): r.size = lhs.size + rhs.size :=
    by
      match r with
      | .Empty =>
        simp at rel
        rw [<- rel.right, <- rel.left]
        unfold size; simp
      | .mk a b a_le_b =>
        simp at rel
        have lhs_rel := rel.left 
        have rhs_rel := rel.right
        set mid := (a+b)/2
        have a_le_mid: a ≤ mid := by 
          apply lower_le_midpoint a_le_b
        simp [lower_le_midpoint a_le_b] at lhs_rel
        match Nat.decLe (mid + 1) b with
        | Decidable.isTrue S_mid_le_b => 
          simp [S_mid_le_b] at rhs_rel
          rw [<- lhs_rel, <- rhs_rel]
          unfold size; simp
          simp [Nat.add_sub_cancel, Nat.add_assoc, Nat.add_comm, Nat.add_sub_assoc,
                a_le_mid, S_mid_le_b, a_le_b]
          rw [<- (Nat.add_sub_assoc a_le_mid)]
          rw [<- (Nat.add_comm (1 + mid - a))]
          rw [(Nat.add_comm 1 mid)]
          rw [<- (Nat.add_sub_assoc S_mid_le_b)]
          rw [<- (Nat.add_comm b)]
          rw [<- (Nat.add_sub_assoc (Nat.le.step a_le_mid))]
          rw [(Nat.add_comm b)]
          rw [(Nat.add_sub_assoc a_le_b)]
          rw [(Nat.add_comm mid.succ)]
          rw [<- (Nat.add_one)]
          rw [(Nat.add_sub_cancel)]
          rw [(Nat.add_comm 1)]
        | Decidable.isFalse nh => 
          have h1: b ≤ mid := by
            apply (Nat.gt_of_not_le) at nh
            apply (GT.gt.lt) at nh
            apply (Nat.le_of_lt_add_one) at nh
            exact nh
          have h2: mid ≤ b := by apply midpoint_le_upper a_le_b
          have b_mid: b = mid := by
            exact (Nat.le_antisymm h1 h2)
          simp [nh] at rhs_rel
          rw [<- lhs_rel, <- rhs_rel]
          unfold size; simp
          rw [<- b_mid]
  end Range


  variable(α: Type)(k: Nat)[Monoid α]

  def update(i: Nat)(val: α)(self: SegmentTree α n): SegmentTree α n :=
    let update_impl(r: Range)
    self

  def query(r: Range)(self: SegmentTree α): α
end SegmentTree

