import RubikSTM.Proofs.Payloads.RowFamily
import Mathlib
import RubikSTM.Definitions.Payloads.Realizes
set_option autoImplicit false

theorem RubikPayload.rowFamily :
    ∀ {n : ℕ} {A Y : Finset (Fin n)} (h : RubikPayload.Admissible A Y)
  (K : ℕ) (σ : Fin n → Equiv.Perm (Fin 24)) (ws : Fin n → List (Rubik.Move n))
  (hcost : ∀ a ∈ A, (ws a).length ≤ K)
  (hstrict : ∀ a ∈ A, RubikBand.StrictControl a (ws a))
  (hact : ∀ a ∈ A, ∀ b ∈ Y, ∀ hb : 0 < b.val ∧ b.val + 1 < n, ∀ i,
    RubikBand.wordPerm (ws a) (RubikGeometry.lab a b i) = RubikGeometry.lab a b (σ a i) ∧
    RubikBand.wordPerm (ws a) (RubikOrbit.minusLab a b hb i) =
      RubikOrbit.minusLab a b hb (σ a i)),
    let U := (A.sort (· ≤ ·)).flatMap ws
  U.length ≤ A.card * K ∧
  (∀ s : Rubik.Sticker n, ¬ RubikBand.Bands A s → RubikBand.wordPerm U s = s) ∧
  (∀ a ∈ A, ∀ b ∈ Y, ∀ hb : 0 < b.val ∧ b.val + 1 < n, ∀ i,
    RubikBand.wordPerm U (RubikGeometry.lab a b i) = RubikGeometry.lab a b (σ a i) ∧
    RubikBand.wordPerm U (RubikOrbit.minusLab a b hb i) =
      RubikOrbit.minusLab a b hb (σ a i)) :=
  @proof_RubikPayload_rowFamily
