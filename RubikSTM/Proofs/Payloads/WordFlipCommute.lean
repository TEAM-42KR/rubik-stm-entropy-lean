import Mathlib
import RubikSTM.Definitions.Payloads.Realizes
import RubikSTM.Lemmas.Intertwiners.SliceCommute
set_option autoImplicit false

theorem proof_RubikPayload_wordFlipCommute {n : ℕ} (b : Fin n) (hb : 0 < b.val ∧ b.val + 1 < n)
  (w : List (Rubik.Move n))
  (hw : ∀ m ∈ w, m.2.1 ≠ b ∧ m.2.1 ≠ b.rev) :
  Commute (RubikBand.wordPerm w) (RubikIntertwiner.surfaceFlip b hb) := by
  have H : Commute (RubikIntertwiner.surfaceFlip b hb) (RubikBand.wordPerm w) := by
    induction w with
    | nil => simp [RubikBand.wordPerm]
    | cons m w ih =>
      have hc := RubikIntertwiner.slice_commute b hb m.1 m.2.1 (hw m (by simp)).1 (hw m (by simp)).2
      have hm : Commute (RubikIntertwiner.surfaceFlip b hb) (Rubik.movePermutation m) :=
        hc.pow_right _
      have ht := ih (by intro v hv; exact hw v (by simp [hv]))
      simpa only [RubikBand.wordPerm, List.map_cons, List.reverse_cons,
        List.prod_append, List.prod_singleton] using ht.mul_right hm
  exact H.symm

#print axioms proof_RubikPayload_wordFlipCommute
