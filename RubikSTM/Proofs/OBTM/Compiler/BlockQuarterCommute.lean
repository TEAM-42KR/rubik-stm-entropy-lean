import Mathlib
import RubikSTM.Definitions.OBTM.Compiler.NativeCoalescedWord
set_option autoImplicit false

theorem proof_RubikOBTMCompiler_block_quarter_commute {n : ℕ} (a : Rubik.Axis) (side₁ side₂ : Bool) (k l : Fin (n-1)) :
  Commute (RubikOBTM.blockQuarter n a side₁ k) (RubikOBTM.blockQuarter n a side₂ l) := by
  have hf (t : Rubik.Sticker n) :
      Rubik.coordinate (Rubik.surfaceRotation n a t).val.1 a = Rubik.coordinate t.val.1 a := by
    fin_cases a <;> simp [Rubik.surfaceRotation,Rubik.rawRotation,Rubik.coordinateRotation,Rubik.coordinate]
  apply Equiv.ext
  intro s
  change RubikOBTM.blockQuarter n a side₁ k (RubikOBTM.blockQuarter n a side₂ l s) =
    RubikOBTM.blockQuarter n a side₂ l (RubikOBTM.blockQuarter n a side₁ k s)
  by_cases hk : RubikOBTM.selected a side₁ k (Rubik.coordinate s.val.1 a) <;>
    by_cases hl : RubikOBTM.selected a side₂ l (Rubik.coordinate s.val.1 a) <;>
    simp [RubikOBTM.blockQuarter,hf,hk,hl]

#print axioms proof_RubikOBTMCompiler_block_quarter_commute
