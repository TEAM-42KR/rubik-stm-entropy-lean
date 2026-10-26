import Mathlib
import RubikSTM.Definitions.Payloads.Realizes
set_option autoImplicit false

theorem proof_RubikPayload_admissibleGeneric {n : ℕ} {A Y : Finset (Fin n)} (h : RubikPayload.Admissible A Y)
  {a b : Fin n} (ha : a ∈ A) (hb : b ∈ Y) : RubikGeometry.Generic n a b := by
  refine ⟨(h.1 a ha).1, (h.2.1 b hb).1, (h.1 a ha).2, (h.2.1 b hb).2, ?_⟩
  intro he
  exact Finset.disjoint_left.mp h.2.2 ha (he ▸ hb)

#print axioms proof_RubikPayload_admissibleGeneric
