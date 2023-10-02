import Lake
open Lake DSL

package «lean4-exercises» {
  -- add any package configuration options here
}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

@[default_target]
lean_lib «Lean4Exercises» {
}

lean_lib Subgroups {
}

lean_lib Usporadani {
}

lean_lib TFAEs {
}

lean_lib PrimeTesting {
}

lean_lib Rings {
}

lean_lib FakeFLT {
}

