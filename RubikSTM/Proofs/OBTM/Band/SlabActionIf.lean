import RubikSTM.Definitions.OBTM.Band.SlabWord
import RubikSTM.Lemmas.OBTM.Band.SlabPermApply
import RubikSTM.Lemmas.OBTM.Band.SlabActionBoth
set_option autoImplicit false
open Rubik RubikConstruction.Control RubikOBTM.Band
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false

theorem proof_RubikOBTM_Band_slab_action_if {n : ℕ} (a u v : Fin n) (h : Admissible n a u v)
    (b d : Fin n) (hb : InInterval u v b) (hd : InInterval u v d) (i : Fin 24) :
    (slabPerm u b (plus a d i) = plus a d ((if d.val ≤ b.val then actualSlabPlus else 1) i)) ∧
    (slabPerm u b (minus a d i) = minus a d ((if d.val ≤ b.val then actualSlabMinus else 1) i)) := by
  have h' : Admissible n a u b := ⟨h.row_pos,h.row_small,h.lower_pos,hb.1,
    by have hv := h.upper_small; have hbb := hb.2; omega,
    by rcases h.row_outside with ho|ho; exact Or.inl ho; exact Or.inr (by have := hb.2; omega)⟩
  by_cases hdb : d.val ≤ b.val
  · simpa only [hdb,if_true] using slab_action_both a u b h' d ⟨hd.1,hdb⟩ i
  · have hu := h'.lower_pos
    have hv := h'.upper_small
    have ha := h'.row_pos
    have has := h'.row_small
    have han := a.isLt
    have hdn := d.isLt
    have ho := h'.row_outside
    have hdlo := hd.1
    have hdhi := hd.2
    have hdmax := h.upper_small
    have hna : ¬ InInterval u b a := by
      rcases ho with ho|ho <;> intro hi <;> rcases hi with ⟨hl,hr⟩ <;> omega
    have hnd : ¬ InInterval u b d := by intro hi; have hh := hi.2; omega
    have hnar : ¬ InInterval u b a.rev := by
      intro hi
      rcases hi with ⟨hl,hr⟩
      simp only [Fin.rev,Fin.val_mk] at hr
      omega
    have hndr : ¬ InInterval u b d.rev := by
      intro hi
      rcases hi with ⟨hl,hr⟩
      simp only [Fin.rev,Fin.val_mk] at hr
      omega
    have hnlo : ¬ InInterval u b (low a) := by
      intro hi
      have hl := hi.1
      simp only [low,Fin.val_mk] at hl
      omega
    have hnhi : ¬ InInterval u b (high a) := by
      intro hi
      have hr := hi.2
      simp only [high,Fin.val_mk] at hr
      omega
    have rl : (low a).rev = high a := by apply Fin.ext; simp [low,high,Fin.rev]
    have rh : (high a).rev = low a := by apply Fin.ext; simp [low,high,Fin.rev]; omega
    fin_cases i <;> constructor <;> rw [slab_perm_apply]
    all_goals simp [plus,minus,lab,rawLab,posTable,normalTable,coordinate,
      hdb,hnd,hna,hnar,hndr,hnlo,hnhi,rl,rh]
