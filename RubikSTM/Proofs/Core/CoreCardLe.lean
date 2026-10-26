import RubikSTM.Definitions.Core.Project
import RubikSTM.Lemmas.Core.LevelCodeInj
set_option autoImplicit false

open Rubik RubikCore

theorem proof_RubikCore_core_card_le (n : ℕ) : Fintype.card (CoreSticker n) ≤ 162 := by
  classical
  let enc : CoreSticker n → Fin 3 × Fin 3 × Fin 3 × Normal := fun s =>
    (levelCode s.val.val.1.1, levelCode s.val.val.1.2.1,
      levelCode s.val.val.1.2.2, s.val.val.2)
  have hinj : Function.Injective enc := by
    intro s t h
    have hx : s.val.val.1.1 = t.val.val.1.1 :=
      RubikCore.levelCode_inj (s.property 0) (t.property 0) (congrArg Prod.fst h)
    have hy : s.val.val.1.2.1 = t.val.val.1.2.1 :=
      RubikCore.levelCode_inj (s.property 1) (t.property 1) (congrArg (fun p => p.2.1) h)
    have hz : s.val.val.1.2.2 = t.val.val.1.2.2 :=
      RubikCore.levelCode_inj (s.property 2) (t.property 2) (congrArg (fun p => p.2.2.1) h)
    have hn : s.val.val.2 = t.val.val.2 := congrArg (fun p => p.2.2.2) h
    apply Subtype.ext
    apply Subtype.ext
    exact Prod.ext (Prod.ext hx (Prod.ext hy hz)) hn
  have hc := Fintype.card_le_of_injective enc hinj
  simpa only [Fintype.card_prod, Fintype.card_fin, Fintype.card_bool] using hc

#print axioms proof_RubikCore_core_card_le
