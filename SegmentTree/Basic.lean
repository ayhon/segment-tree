open Mathlib.Algebra.Group.Defs

structure SegmentTree(α : Type) where
  v: Array α
deriving Repr

namespace SegmentTree
  def update(i: Nat)(val: α)(self: SegmentTree α): SegmentTree α :=
    self

  def query(b e: Nat)(self: SegmentTree α)/-: α -/:= self.v[b]?
end SegmentTree
