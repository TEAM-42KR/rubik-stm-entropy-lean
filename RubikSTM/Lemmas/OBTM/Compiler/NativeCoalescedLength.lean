import RubikSTM.Proofs.OBTM.Compiler.NativeCoalescedLength
import Mathlib
import RubikSTM.Definitions.OBTM.Compiler.NativeCoalescedWord
set_option autoImplicit false

theorem RubikOBTMCompiler.native_coalesced_length :
    ∀ {n : ℕ} (a : Rubik.Axis) (side : Bool) (lower : Fin (n-1))
  (B : List (Fin (n-1))), (RubikOBTMCompiler.nativeCoalescedWord a side lower B).length = B.length+B.length%2 ∧
    (RubikOBTMCompiler.nativeCoalescedWord a side lower B).length ≤ B.length+1 :=
  @proof_RubikOBTMCompiler_native_coalesced_length
