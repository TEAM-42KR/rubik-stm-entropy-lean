import RubikSTM.Proofs.OBTM.Compiler.SlabBaselineTwo
import Mathlib
import RubikSTM.Definitions.OBTM.Compiler.NativeCoalescedWord
set_option autoImplicit false

theorem RubikOBTMCompiler.slab_baseline_two :
    ∀ {n : ℕ} (a : Rubik.Axis) (side : Bool) (lower : Fin (n-1))
  (B : List (Fin (n-1))), RubikOBTMCompiler.slabBaseline a side lower B ^ 2 = 1 :=
  @proof_RubikOBTMCompiler_slab_baseline_two
