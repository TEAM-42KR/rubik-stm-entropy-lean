import RubikSTM.Definitions.OBTM.Band.SlabWord
import RubikSTM.Lemmas.OBTM.ParallelSlicesApply
set_option autoImplicit false
open scoped Classical
open Rubik RubikOBTM RubikOBTM.Band
set_option maxHeartbeats 600000

theorem proof_RubikOBTM_Band_slab_perm_apply {n : ℕ} (u v : Fin n) (s : Sticker n) :
    slabPerm u v s = if InInterval u v (coordinate s.val.1 2).rev then
      surfaceRotation n 2 s else s := by
  have hi : coordinate s.val.1 2 ∈ slabDepths u v ↔
      InInterval u v (coordinate s.val.1 2).rev := by
    constructor
    · intro hm
      obtain ⟨d,hd,he⟩ := Finset.mem_image.mp hm
      rw [← he, Fin.rev_rev]
      exact ⟨(Finset.mem_Icc.mp hd).1,(Finset.mem_Icc.mp hd).2⟩
    · intro hm
      exact Finset.mem_image.mpr ⟨(coordinate s.val.1 2).rev,
        Finset.mem_Icc.mpr hm, by simp⟩
  have hc := RubikOBTM.parallel_slices_apply 2 ((slabDepths u v).sort (· ≤ ·))
    (Finset.sort_nodup _ _) 1 s
  simpa [slabPerm, RubikBand.parallelBaseline, hi] using hc
