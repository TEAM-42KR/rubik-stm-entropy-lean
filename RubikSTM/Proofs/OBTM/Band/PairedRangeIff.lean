import RubikSTM.Definitions.OBTM.Band.CleanAction
import RubikSTM.Lemmas.OBTM.Band.SingleIntersectionRange
set_option autoImplicit false
open Rubik RubikOBTM.Band

theorem proof_RubikOBTM_Band_paired_range_iff {n : ℕ} (a u v : Fin n) (h : Admissible n a u v)
    (s : Sticker n) : s ∈ PairedRange a u v ↔ RubikBand.Band a s ∧ ColumnBand u v s := by
  have helper (d : Fin n) (hd : InInterval u v d) :
      (RubikBand.Band a s ∧ RubikBand.Band d s) ↔
      (s ∈ Set.range (plus a d) ∨ s ∈ Set.range (minus a d)) := by
    apply single_intersection_range a d h.row_pos (le_trans h.lower_pos hd.1)
      h.row_small (by have hv := h.upper_small; have hdv := hd.2; omega) ?_ s
    intro he
    have he' := congrArg Fin.val he
    have ho := h.row_outside
    rcases hd with ⟨hu,hv⟩
    rcases ho with ho|ho <;> omega
  constructor
  · rintro ⟨d,hd,hs⟩
    have he := (helper d hd).mpr hs
    exact ⟨he.1,d,hd,he.2⟩
  · rintro ⟨ha,d,hd,hs⟩
    exact ⟨d,hd,(helper d hd).mp ⟨ha,hs⟩⟩
