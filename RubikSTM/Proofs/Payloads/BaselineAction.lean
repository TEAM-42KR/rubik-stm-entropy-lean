import Mathlib
import RubikSTM.Definitions.Payloads.Realizes
import RubikSTM.Lemmas.Payloads.AdmissibleGeneric
import RubikSTM.Lemmas.Payloads.LabelOutsideThirdBand
import RubikSTM.Lemmas.Orbits.FlipLabel
import RubikSTM.Lemmas.Orbits.PairedQuarter
import RubikSTM.Lemmas.Payloads.SingleIndexWordAction
set_option autoImplicit false

theorem proof_RubikPayload_baselineAction {n : ℕ} {A Y : Finset (Fin n)} (h : RubikPayload.Admissible A Y)
  {a b : Fin n} (ha : a ∈ A) (hbY : b ∈ Y)
  (hb : 0 < b.val ∧ b.val + 1 < n) (i : Fin 24) :
  RubikPayload.columnBaseline Y (RubikGeometry.lab a b i) = RubikGeometry.lab a b (RubikGeometry.gen7 i) ∧
  RubikPayload.columnBaseline Y (RubikOrbit.minusLab a b hb i) =
    RubikOrbit.minusLab a b hb (RubikOrbit.minusB i) := by
  have hg := RubikPayload.admissibleGeneric h ha hbY
  have hgs : RubikGeometry.Generic n b a := ⟨hg.one_le_b,hg.one_le_a,hg.b_small,hg.a_small,Ne.symm hg.ne⟩
  have hstep : ∀ c ∈ Y, ∀ i,
      RubikBand.wordPerm [(2,c.rev,0)] (RubikGeometry.lab a b i) =
        RubikGeometry.lab a b (if c=b then RubikGeometry.gen7 i else i) ∧
      RubikBand.wordPerm [(2,c.rev,0)] (RubikOrbit.minusLab a b hb i) =
        RubikOrbit.minusLab a b hb (if c=b then RubikOrbit.minusB i else i) := by
    intro c hc i
    by_cases he : c=b
    · subst c
      simpa [RubikBand.wordPerm, Rubik.movePermutation] using RubikOrbit.pairedQuarter hg hb i
    · have hca : c ≠ a := by
        intro heq
        exact Finset.disjoint_left.mp h.2.2 ha (heq ▸ hc)
      have hp := RubikPayload.labelOutsideThirdBand hg (h.2.1 c hc) hca he i
      have hm : ¬ RubikBand.Band c (RubikOrbit.minusLab a b hb i) := by
        rw [RubikOrbit.flipLabel hg hb]
        exact RubikPayload.labelOutsideThirdBand hgs (h.2.1 c hc) he hca _
      have fp : Rubik.coordinate (RubikGeometry.lab a b i).val.1 2 ≠ c.rev := by
        intro heq; exact hp ⟨2,Or.inr heq⟩
      have fm : Rubik.coordinate (RubikOrbit.minusLab a b hb i).val.1 2 ≠ c.rev := by
        intro heq; exact hm ⟨2,Or.inr heq⟩
      simp [RubikBand.wordPerm, Rubik.movePermutation, Rubik.sliceQuarter, he, fp, fm]
  have hp := RubikPayload.singleIndexWordAction (Y.sort (· ≤ ·)) (Finset.sort_nodup _ _)
    b (fun c => [(2,c.rev,0)]) (RubikGeometry.lab a b) RubikGeometry.gen7 (by
      intro c hc i; exact (hstep c (by simpa using hc) i).1) i
  have hm := RubikPayload.singleIndexWordAction (Y.sort (· ≤ ·)) (Finset.sort_nodup _ _)
    b (fun c => [(2,c.rev,0)]) (RubikOrbit.minusLab a b hb) RubikOrbit.minusB (by
      intro c hc i; exact (hstep c (by simpa using hc) i).2) i
  constructor
  · simpa [RubikPayload.columnBaseline, RubikPayload.baselineWord, hbY, ← List.map_eq_flatMap] using hp
  · simpa [RubikPayload.columnBaseline, RubikPayload.baselineWord, hbY, ← List.map_eq_flatMap] using hm

#print axioms proof_RubikPayload_baselineAction
