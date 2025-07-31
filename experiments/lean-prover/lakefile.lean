import Lake

open Lake DSL

def linkArgs :=
  if System.Platform.isWindows then
    panic! "Windows is not supported!"
  else if System.Platform.isOSX then
    #["-L/opt/homebrew/opt/openblas/lib", "-L/usr/local/opt/openblas/lib", "-lblas"]
  else -- Linux
    #["-L/usr/lib/x86_64-linux-gnu/", "-lblas", "-lm"]

package "lean-prover" {
  moreLinkArgs := linkArgs
}

require scilean from git "https://github.com/lecopivo/SciLean" @ "v4.20.1"

@[default_target]
lean_lib LeanProver {
  roots := #[`LeanProver]
}

-- require smt from
--   git "https://github.com/ufmg-smite/lean-smt.git" @ "main"

require mathlib from
  git "https://github.com/leanprover-community/mathlib4.git"

require "marcusrossel" / "egg" @ git "main"
