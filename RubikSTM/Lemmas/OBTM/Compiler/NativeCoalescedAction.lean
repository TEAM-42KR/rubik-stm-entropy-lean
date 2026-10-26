import RubikSTM.Proofs.OBTM.Compiler.NativeCoalescedAction
import Mathlib
import RubikSTM.Definitions.OBTM.Compiler.NativeCoalescedWord
set_option autoImplicit false

theorem RubikOBTMCompiler.native_coalesced_action :
    ∀ {n : ℕ} (a : Rubik.Axis) (side : Bool) (lower : Fin (n-1))
  (B : List (Fin (n-1))), RubikOBTM.Band.wordPerm (RubikOBTMCompiler.nativeCoalescedWord a side lower B) =
    RubikOBTMCompiler.slabBaseline a side lower B :=
  @proof_RubikOBTMCompiler_native_coalesced_action
