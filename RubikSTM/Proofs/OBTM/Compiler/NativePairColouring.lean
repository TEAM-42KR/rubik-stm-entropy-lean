import Mathlib
import RubikSTM.Definitions.OBTM.Compiler.NativeProgram
import RubikSTM.Lemmas.OBTM.Band.WordPermApply
set_option autoImplicit false

theorem proof_RubikOBTMCompiler_native_pair_colouring {n : ℕ} (a b : Fin n)
  (w : List (RubikOBTM.BlockMove n)) (g : RubikPayload.Pair)
  (h : RubikOBTMCompiler.NativeActsPair a b w g) (c : Rubik.Colouring n) :
  RubikOBTMCompiler.commonView (RubikOBTM.applyBlockWord w c) a b =
    RubikRectangle.rawAction g (RubikOBTMCompiler.commonView c a b) := by
  have hp (i : Fin 24) :
      (RubikOBTM.Band.wordPerm w)⁻¹ (RubikOBTM.Band.plus a b i) =
        RubikOBTM.Band.plus a b (g.1⁻¹ i) := by
    apply (RubikOBTM.Band.wordPerm w).injective
    simpa using (h.1 (g.1⁻¹ i)).symm
  have hm (i : Fin 24) :
      (RubikOBTM.Band.wordPerm w)⁻¹ (RubikOBTM.Band.minus a b i) =
        RubikOBTM.Band.minus a b (g.2⁻¹ i) := by
    apply (RubikOBTM.Band.wordPerm w).injective
    simpa using (h.2 (g.2⁻¹ i)).symm
  apply Prod.ext
  · funext i
    change RubikOBTM.applyBlockWord w c (RubikOBTM.Band.plus a b i) = c (RubikOBTM.Band.plus a b (g.1⁻¹ i))
    rw [RubikOBTM.Band.wordPerm_apply,hp]
  · funext i
    change RubikOBTM.applyBlockWord w c (RubikOBTM.Band.minus a b i) = c (RubikOBTM.Band.minus a b (g.2⁻¹ i))
    rw [RubikOBTM.Band.wordPerm_apply,hm]

#print axioms proof_RubikOBTMCompiler_native_pair_colouring
