import Lake
open Lake DSL

package "segment-tree" where
  -- Settings applied to both builds and interactive editing
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩ -- pretty-prints `fun a ↦ b`
  ]
  -- add any additional package configuration options here

-- require "leanprover-community" / "mathlib"
require mathlib from
  ".."/".."/".."/"git"/"mathlib4"



@[default_target]
lean_lib «SegmentTree» where
  -- add any library configuration options here
