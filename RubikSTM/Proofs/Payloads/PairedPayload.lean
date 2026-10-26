import Mathlib
import RubikSTM.Definitions.Payloads.Realizes
import RubikSTM.Lemmas.Payloads.UniformDiagonalControls
import RubikSTM.Lemmas.Payloads.DiagonalConjugator
import RubikSTM.Lemmas.Payloads.RowFamily
import RubikSTM.Lemmas.Payloads.AdmissibleGeneric
import RubikSTM.Lemmas.Payloads.InverseWordPermutation
import RubikSTM.Lemmas.Payloads.BaselinePhysical
import RubikSTM.Lemmas.Payloads.ConjugatePayload
set_option autoImplicit false

theorem proof_RubikPayload_pairedPayload : ∃ C : ℕ, ∀ (n : ℕ) (A Y : Finset (Fin n)),
  RubikPayload.Admissible A Y → ∀ g : Fin n → RubikPayload.Pair,
    (∀ a ∈ A, g a ∈ RubikChannel.disjointFourCycleAlphabet (Fin 24)) →
    ∃ w : List (Rubik.Move n), w.length ≤ Y.card + C * (A.card + 1) ∧
      RubikPayload.Realizes A Y g w := by
  classical
  obtain ⟨K,hK⟩ := RubikPayload.uniformDiagonalControls
  refine ⟨2*K, ?_⟩
  intro n A Y h g hg
  have rows : ∀ a : Fin n, ∃ σ : Equiv.Perm (Fin 24), ∃ w : List (Rubik.Move n),
      a ∈ A → w.length ≤ K ∧ RubikBand.StrictControl a w ∧
      (∀ b : Fin n, RubikGeometry.Generic n a b →
        (∀ i, RubikBand.wordPerm w (RubikGeometry.lab a b i) = RubikGeometry.lab a b (σ i)) ∧
        (∀ hb : 0 < b.val ∧ b.val+1 < n, ∀ i,
          RubikBand.wordPerm w (RubikOrbit.minusLab a b hb i) = RubikOrbit.minusLab a b hb (σ i))) ∧
      (σ * RubikGeometry.gen7 * σ⁻¹ = (g a).1 ∧ σ * RubikOrbit.minusB * σ⁻¹ = (g a).2) := by
    intro a
    by_cases ha : a ∈ A
    · obtain ⟨σ,hσ⟩ := RubikPayload.diagonalConjugator (g a) (hg a ha)
      obtain ⟨w,hw,hs,hact⟩ := hK n a (h.1 a ha) σ
      exact ⟨σ,w,fun _ => ⟨hw,hs,hact,hσ⟩⟩
    · exact ⟨1,[],fun ha' => (ha ha').elim⟩
  choose σ ws hrs using rows
  let U := (A.sort (· ≤ ·)).flatMap ws
  have H := RubikPayload.rowFamily h K σ ws (fun a ha => (hrs a ha).1)
    (fun a ha => (hrs a ha).2.1) (by
      intro a ha b hbY hb i
      have hc := (hrs a ha).2.2.1 b (RubikPayload.admissibleGeneric h ha hbY)
      exact ⟨hc.1 i, hc.2 hb i⟩)
  refine ⟨RubikPayload.inverseWord U ++ RubikPayload.baselineWord Y ++ U, ?_, ?_⟩
  · have hU : U.length ≤ A.card*K := H.1
    rw [List.length_append, List.length_append, (RubikPayload.inverseWordPermutation U).2,
      (RubikPayload.baselinePhysical Y).1]
    nlinarith
  · exact RubikPayload.conjugatePayload h g σ U H.2.1 H.2.2
      (fun a ha => (hrs a ha).2.2.2)

#print axioms proof_RubikPayload_pairedPayload
