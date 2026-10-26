import RubikSTM.Proofs.OBTM.Global.SequentialRecolour
import RubikSTM.Definitions.OBTM.Global.RectangleCompiler
set_option autoImplicit false

theorem RubikOBTM.Global.sequential_recolour :
    ∀ {n : ℕ} {J : Type*} (S : J → Set (Rubik.Sticker n)) (cost : J → ℕ) (d : Rubik.Position n) (rows : List J) (hnd : rows.Nodup) (hdis : ∀ i ∈ rows, ∀ j ∈ rows, i ≠ j → Disjoint (S i) (S j)) (hsolve : ∀ i ∈ rows, ∀ c : Rubik.Position n, ∃ w : List (RubikOBTM.BlockMove n), w.length ≤ cost i ∧ RubikOBTM.Global.Recolour (S i) c.val d.val w) (c : Rubik.Position n), ∃ w : List (RubikOBTM.BlockMove n), w.length ≤ (rows.map cost).sum ∧ RubikOBTM.Global.Recolour (⋃ i ∈ rows, S i) c.val d.val w :=
  @proof_RubikOBTM_Global_sequential_recolour
