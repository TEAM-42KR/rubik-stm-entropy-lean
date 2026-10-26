import RubikSTM.Proofs.Payloads.ConjugatePayload
import Mathlib
import RubikSTM.Definitions.Payloads.Realizes
set_option autoImplicit false

theorem RubikPayload.conjugatePayload :
    ∀ {n : ℕ} {A Y : Finset (Fin n)} (h : RubikPayload.Admissible A Y)
  (g : Fin n → RubikPayload.Pair) (σ : Fin n → Equiv.Perm (Fin 24))
  (U : List (Rubik.Move n))
  (hfix : ∀ s : Rubik.Sticker n, ¬ RubikBand.Bands A s → RubikBand.wordPerm U s = s)
  (hact : ∀ a ∈ A, ∀ b ∈ Y, ∀ hb : 0 < b.val ∧ b.val + 1 < n, ∀ i,
    RubikBand.wordPerm U (RubikGeometry.lab a b i) = RubikGeometry.lab a b (σ a i) ∧
    RubikBand.wordPerm U (RubikOrbit.minusLab a b hb i) =
      RubikOrbit.minusLab a b hb (σ a i))
  (hconj : ∀ a ∈ A, σ a * RubikGeometry.gen7 * (σ a)⁻¹ = (g a).1 ∧
    σ a * RubikOrbit.minusB * (σ a)⁻¹ = (g a).2), RubikPayload.Realizes A Y g
    (RubikPayload.inverseWord U ++ RubikPayload.baselineWord Y ++ U) :=
  @proof_RubikPayload_conjugatePayload
