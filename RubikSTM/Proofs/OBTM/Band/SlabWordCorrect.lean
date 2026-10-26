import RubikSTM.Definitions.OBTM.Band.SlabWord
import RubikSTM.Lemmas.OBTM.Band.SlabPrefixDifference
import RubikSTM.Lemmas.OBTM.Compiler.BlockQuarterCommute
import RubikSTM.Lemmas.OBTM.Compiler.BlockQuarterFour
set_option autoImplicit false
open Rubik RubikOBTM RubikOBTM.Band

theorem proof_RubikOBTM_Band_slab_word_correct {n : ℕ} (a u v : Fin n) (h : Admissible n a u v) :
    (slabWord a u v h).length = 2 ∧ wordPerm (slabWord a u v h) = slabPerm u v := by
  refine ⟨rfl,?_⟩
  have hv : v.val < n-1 := by have := h.upper_small; omega
  let ku : Fin (n-1) := ⟨u.val-1,by have := h.lower_pos; have := h.ordered; omega⟩
  let kv : Fin (n-1) := ⟨v.val,hv⟩
  have hi : (blockQuarter n 2 true ku)^3 = (blockQuarter n 2 true ku)⁻¹ := by
    apply eq_inv_iff_mul_eq_one.mpr
    rw [← pow_succ]
    exact RubikOBTMCompiler.block_quarter_four 2 true ku
  rw [slab_prefix_difference u v h.lower_pos h.ordered hv]
  change (blockQuarter n 2 true ku)^3 * blockQuarter n 2 true kv =
    blockQuarter n 2 true kv * (blockQuarter n 2 true ku)⁻¹
  rw [hi]
  exact (RubikOBTMCompiler.block_quarter_commute 2 true true kv ku).inv_right.eq.symm
