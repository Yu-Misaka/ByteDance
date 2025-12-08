import Lake
open Lake DSL

package "ByteDance" where
  -- Settings applied to both builds and interactive editing
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩ -- pretty-prints `fun a ↦ b`
  ]
  -- add any additional package configuration options here

require "leanprover-community" / "mathlib" @ "git#0d837987e5971c0b4a1bb468cd3409bcc4112301"

@[default_target]
lean_lib «ByteDance» where
  -- add any library configuration options here
