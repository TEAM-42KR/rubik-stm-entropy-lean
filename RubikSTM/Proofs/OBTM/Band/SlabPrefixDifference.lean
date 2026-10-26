import RubikSTM.Definitions.OBTM.Band.SlabWord
import RubikSTM.Lemmas.OBTM.Band.SlabPermApply
set_option autoImplicit false
open scoped Classical
open Rubik RubikOBTM RubikOBTM.Band
set_option maxHeartbeats 600000

theorem proof_RubikOBTM_Band_slab_prefix_difference {n : ℕ} (u v : Fin n)
    (hu : 1 ≤ u.val) (huv : u.val ≤ v.val) (hv : v.val < n-1) :
    slabPerm u v = blockQuarter n 2 true ⟨v.val,hv⟩ *
      (blockQuarter n 2 true ⟨u.val-1,by omega⟩)⁻¹ := by
  let ku : Fin (n-1) := ⟨u.val-1,by omega⟩
  let kv : Fin (n-1) := ⟨v.val,hv⟩
  have hf (t : Sticker n) : coordinate (surfaceRotation n 2 t).val.1 2 = coordinate t.val.1 2 := by
    simp [surfaceRotation,rawRotation,coordinateRotation,coordinate]
  have hb (t : Sticker n) : coordinate ((surfaceRotation n 2).symm t).val.1 2 = coordinate t.val.1 2 := by
    simpa only [Equiv.apply_symm_apply] using (hf ((surfaceRotation n 2).symm t)).symm
  apply Equiv.ext
  intro s
  change slabPerm u v s = (blockQuarter n 2 true kv) ((blockQuarter n 2 true ku)⁻¹ s)
  rw [slab_perm_apply]
  have hi : InInterval u v (coordinate s.val.1 2).rev ↔
      selected 2 true kv (coordinate s.val.1 2) ∧ ¬ selected 2 true ku (coordinate s.val.1 2) := by
    have hz := (coordinate s.val.1 2).isLt
    dsimp [InInterval,selected,ku,kv]
    try simp only [Fin.rev,Fin.val_mk]
    omega
  have hsub : selected 2 true ku (coordinate s.val.1 2) → selected 2 true kv (coordinate s.val.1 2) := by
    dsimp [selected,ku,kv]
    omega
  by_cases hl : selected 2 true ku (coordinate s.val.1 2)
  · have hlo : (blockQuarter n 2 true ku)⁻¹ s = (surfaceRotation n 2).symm s := by
      change (if selected 2 true ku (coordinate s.val.1 2) then (surfaceRotation n 2).symm s else s) = _
      simp [hl]
    have hhi : selected 2 true kv (coordinate ((surfaceRotation n 2).symm s).val.1 2) := by
      rw [hb]
      exact hsub hl
    have hn : ¬ InInterval u v (coordinate s.val.1 2).rev := fun hh => (hi.mp hh).2 hl
    rw [if_neg hn,hlo]
    simp [blockQuarter,hhi]
  · have hlo : (blockQuarter n 2 true ku)⁻¹ s = s := by
      change (if selected 2 true ku (coordinate s.val.1 2) then (surfaceRotation n 2).symm s else s) = _
      simp [hl]
    rw [hlo]
    by_cases hh : selected 2 true kv (coordinate s.val.1 2)
    · rw [if_pos (hi.mpr ⟨hh,hl⟩)]
      simp [blockQuarter,hh]
    · have hn : ¬ InInterval u v (coordinate s.val.1 2).rev := fun hx => hh (hi.mp hx).1
      rw [if_neg hn]
      simp [blockQuarter,hh]
