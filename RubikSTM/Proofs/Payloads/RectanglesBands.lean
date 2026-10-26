import Mathlib
import RubikSTM.Definitions.Payloads.Realizes
import RubikSTM.Lemmas.Orbits.BandIntersection
import RubikSTM.Lemmas.Payloads.AdmissibleGeneric
set_option autoImplicit false

theorem proof_RubikPayload_rectanglesBands {n : ℕ} {A Y : Finset (Fin n)} (h : RubikPayload.Admissible A Y)
  (s : Rubik.Sticker n) : RubikPayload.Rectangles A Y s ↔
    RubikBand.Bands A s ∧ RubikBand.Bands Y s := by
  constructor
  · rintro ⟨a,ha,b,hb,hs⟩
    have hh := (RubikOrbit.bandIntersection (RubikPayload.admissibleGeneric h ha hb) s).mpr hs
    exact ⟨⟨a,ha,hh.1⟩,⟨b,hb,hh.2⟩⟩
  · rintro ⟨⟨a,ha,has⟩,⟨b,hb,hbs⟩⟩
    exact ⟨a,ha,b,hb,(RubikOrbit.bandIntersection (RubikPayload.admissibleGeneric h ha hb) s).mp ⟨has,hbs⟩⟩

#print axioms proof_RubikPayload_rectanglesBands
