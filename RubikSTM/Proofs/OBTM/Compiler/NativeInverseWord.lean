import Mathlib
import RubikSTM.Definitions.OBTM.Compiler.NativeCoalescedWord
import RubikSTM.Lemmas.OBTM.BlockInverse
set_option autoImplicit false

theorem proof_RubikOBTMCompiler_native_inverse_word {n : ℕ} (U : List (RubikOBTM.BlockMove n)) :
  ∃ V : List (RubikOBTM.BlockMove n), V.length=U.length ∧
    RubikOBTM.Band.wordPerm V = (RubikOBTM.Band.wordPerm U)⁻¹ := by
  induction U with
  | nil => exact ⟨[],rfl,by simp [RubikOBTM.Band.wordPerm]⟩
  | cons m U ih =>
    obtain ⟨V,hL,hV⟩ := ih
    obtain ⟨r,hr⟩ := RubikOBTM.block_inverse m
    refine ⟨V++[r],by simp [hL],?_⟩
    simp [RubikOBTM.Band.wordPerm,List.reverse_cons,List.reverse_append,hr,hV,
      show (V.map RubikOBTM.blockPermutation).reverse.prod = (RubikOBTM.Band.wordPerm U)⁻¹ from hV]

#print axioms proof_RubikOBTMCompiler_native_inverse_word
