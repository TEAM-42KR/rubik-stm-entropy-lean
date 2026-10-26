import Mathlib
import RubikSTM.Definitions.OBTM.Compiler.NativeCoalescedWord
set_option autoImplicit false

theorem proof_RubikOBTMCompiler_native_coalesced_length {n : ℕ} (a : Rubik.Axis) (side : Bool) (lower : Fin (n-1))
  (B : List (Fin (n-1))) :
  (RubikOBTMCompiler.nativeCoalescedWord a side lower B).length = B.length+B.length%2 ∧
    (RubikOBTMCompiler.nativeCoalescedWord a side lower B).length ≤ B.length+1 := by
  have hm : B.length%2<2 := Nat.mod_lt _ (by decide)
  by_cases he : B.length%2=0
  · simp [RubikOBTMCompiler.nativeCoalescedWord,he]
  · have ho : B.length%2=1 := by omega
    simp [RubikOBTMCompiler.nativeCoalescedWord,he,ho,Nat.add_comm]

#print axioms proof_RubikOBTMCompiler_native_coalesced_length
