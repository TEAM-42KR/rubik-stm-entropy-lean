import RubikSTM.Proofs.GlobalWords.SequentialRecolour
import Mathlib
import RubikSTM.Definitions.GlobalWords.Region
set_option autoImplicit false

theorem RubikGlobalWord.sequential_recolour :
    ∀ {n : ℕ} {J : Type*} (S : J → Set (Rubik.Sticker n))
  (cost : J → ℕ) (d : Rubik.Position n) (rows : List J) (hnd : rows.Nodup)
  (hdis : ∀ i ∈ rows, ∀ j ∈ rows, i ≠ j → Disjoint (S i) (S j))
  (hsolve : ∀ i ∈ rows, ∀ c : Rubik.Position n, ∃ w : List (Rubik.Move n),
    w.length ≤ cost i ∧ RubikGlobalWord.Recolour (S i) c.val d.val w), ∀ c : Rubik.Position n, ∃ w : List (Rubik.Move n),
    w.length ≤ (rows.map cost).sum ∧
      RubikGlobalWord.Recolour {s | ∃ i ∈ rows, s ∈ S i} c.val d.val w :=
  @proof_RubikGlobalWord_sequential_recolour
