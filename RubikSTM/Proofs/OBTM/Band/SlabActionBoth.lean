import RubikSTM.Definitions.OBTM.Band.SlabWord
import RubikSTM.Lemmas.OBTM.Band.SlabPermApply
set_option autoImplicit false
open Rubik RubikConstruction.Control RubikOBTM.Band
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

theorem proof_RubikOBTM_Band_slab_action_both {n : ℕ} (a u v : Fin n) (h : Admissible n a u v)
    (d : Fin n) (hd : InInterval u v d) (i : Fin 24) :
    (slabPerm u v (plus a d i) = plus a d (actualSlabPlus i)) ∧
    (slabPerm u v (minus a d i) = minus a d (actualSlabMinus i)) := by
  have hu := h.lower_pos
  have hv := h.upper_small
  have ha := h.row_pos
  have has := h.row_small
  have han := a.isLt
  have hdn := d.isLt
  have ho := h.row_outside
  have hdlo := hd.1
  have hdhi := hd.2
  have hna : ¬ InInterval u v a := by
    rcases ho with ho|ho <;> intro hi <;> rcases hi with ⟨hl,hr⟩ <;> omega
  have hnar : ¬ InInterval u v a.rev := by
    intro hi
    rcases hi with ⟨hl,hr⟩
    simp only [Fin.rev,Fin.val_mk] at hr
    omega
  have hndr : ¬ InInterval u v d.rev := by
    intro hi
    rcases hi with ⟨hl,hr⟩
    simp only [Fin.rev,Fin.val_mk] at hr
    omega
  have hnlo : ¬ InInterval u v (low a) := by
    intro hi
    have hl := hi.1
    simp only [low,Fin.val_mk] at hl
    omega
  have hnhi : ¬ InInterval u v (high a) := by
    intro hi
    have hr := hi.2
    simp only [high,Fin.val_mk] at hr
    omega
  have rl : (low a).rev = high a := by
    apply Fin.ext
    simp [low,high,Fin.rev]
  have rh : (high a).rev = low a := by
    apply Fin.ext
    simp [low,high,Fin.rev]
    omega
  fin_cases i <;> constructor <;> rw [slab_perm_apply]
  all_goals simp [plus,minus,lab,rawLab,posTable,normalTable,coordinate,
    hd,hna,hnar,hndr,hnlo,hnhi,rl,rh,actualSlabPlus,actualSlabMinus,
    Equiv.swap_apply_def,surfaceRotation,rawRotation,coordinateRotation,normalRotation,
    normalForward]
