import RubikSTM.Definitions.Rectangles.PayloadInterface
import RubikSTM.Lemmas.Payloads.LabelOutsideThirdBand
import RubikSTM.Lemmas.Orbits.FlipLabel
set_option autoImplicit false

theorem proof_RubikRectangle_labels_outside_bands {n : ℕ} {a b : Fin n} (hg : RubikGeometry.Generic n a b)
    (hb : 0 < b.val ∧ b.val + 1 < n) (H : Finset (Fin n))
    (hH : ∀ c ∈ H, RubikPayload.Half c) (haH : a ∉ H) (hbH : b ∉ H) (i : Fin 24) :
    ¬ RubikBand.Bands H (RubikGeometry.lab a b i) ∧
      ¬ RubikBand.Bands H (RubikOrbit.minusLab a b hb i) := by
  have hswap : RubikGeometry.Generic n b a :=
    ⟨hg.one_le_b,hg.one_le_a,hg.b_small,hg.a_small,Ne.symm hg.ne⟩
  constructor
  · rintro ⟨c,hc,hband⟩
    exact RubikPayload.labelOutsideThirdBand hg (hH c hc)
      (fun h => haH (h ▸ hc)) (fun h => hbH (h ▸ hc)) i hband
  · rw [RubikOrbit.flipLabel hg hb]
    rintro ⟨c,hc,hband⟩
    exact RubikPayload.labelOutsideThirdBand hswap (hH c hc)
      (fun h => hbH (h ▸ hc)) (fun h => haH (h ▸ hc)) _ hband

#print axioms proof_RubikRectangle_labels_outside_bands
