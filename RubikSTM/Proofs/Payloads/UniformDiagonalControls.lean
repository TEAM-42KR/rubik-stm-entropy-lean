import Mathlib
import RubikSTM.Definitions.Payloads.Realizes
import RubikSTM.Lemmas.Construction.Control.Physical.UniformSignedModel
import RubikSTM.Lemmas.Payloads.SignedStrict
import RubikSTM.Lemmas.Payloads.ChronologicalWord
import RubikSTM.Lemmas.Construction.Control.Physical.ActualMovesEval
import RubikSTM.Lemmas.Construction.Control.Physical.WordAction
import RubikSTM.Lemmas.Construction.Control.Physical.LabelsEqT
import RubikSTM.Lemmas.Payloads.CommonMinusAction
set_option autoImplicit false

theorem proof_RubikPayload_uniformDiagonalControls : ∃ K : ℕ, ∀ (n : ℕ) (a : Fin n), RubikPayload.Half a →
  ∀ σ : Equiv.Perm (Fin 24), ∃ w : List (Rubik.Move n),
    w.length ≤ K ∧ RubikBand.StrictControl a w ∧
    ∀ (b : Fin n), RubikGeometry.Generic n a b →
      (∀ i, RubikBand.wordPerm w (RubikGeometry.lab a b i) = RubikGeometry.lab a b (σ i)) ∧
      (∀ hb : 0 < b.val ∧ b.val + 1 < n, ∀ i,
        RubikBand.wordPerm w (RubikOrbit.minusLab a b hb i) =
          RubikOrbit.minusLab a b hb (σ i)) := by
  obtain ⟨K,hK⟩ := RubikConstruction.Control.Physical.uniform_signed_model
  refine ⟨K, ?_⟩
  intro n a ha σ
  obtain ⟨letters,hL,hσ,hd⟩ := hK σ
  let w := RubikConstruction.Control.Physical.actualMoves a letters
  have hs : RubikBand.StrictControl a w := RubikPayload.signedStrict a ha letters hd
  refine ⟨w, ?_, hs, ?_⟩
  · simpa [w, RubikConstruction.Control.Physical.actualMoves] using hL
  · intro b hg
    have hplus : ∀ i, RubikBand.wordPerm w (RubikGeometry.lab a b i) = RubikGeometry.lab a b (σ i) := by
      intro i
      rw [← RubikPayload.chronologicalWord]
      change RubikConstruction.Control.Physical.chronological
        (RubikConstruction.Control.Physical.actualMoves a letters) _ = _
      rw [RubikConstruction.Control.Physical.actual_moves_eval]
      have h := RubikConstruction.Control.Physical.word_action a b hg.one_le_a hg.one_le_b
        hg.a_small hg.b_small hg.ne (FreeGroup.mk letters) i
      simpa only [RubikConstruction.Control.Physical.labels_eq_T, hσ] using h
    exact ⟨hplus, fun hb => RubikPayload.commonMinusAction hg hb w hs.1 σ hplus⟩

#print axioms proof_RubikPayload_uniformDiagonalControls
