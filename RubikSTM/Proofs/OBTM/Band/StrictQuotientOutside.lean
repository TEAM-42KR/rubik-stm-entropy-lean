import RubikSTM.Definitions.OBTM.Band.SlabWord
import RubikSTM.Lemmas.OBTM.Band.PairedRangeIff
import RubikSTM.Lemmas.OBTM.Band.SlabBandsIff
import RubikSTM.Lemmas.OBTM.Bands.ConjugationOutside
import RubikSTM.Lemmas.OBTM.Bands.BaselineBand
set_option autoImplicit false
open Rubik RubikOBTM.Band
set_option maxHeartbeats 600000

theorem proof_RubikOBTM_Band_strict_quotient_outside {n : ℕ} (a u v : Fin n)
    (h : Admissible n a u v) (w z : List (Move n))
    (hw : RubikBand.StrictControl a w) (hz : RubikBand.StrictControl a z)
    (s : Sticker n) (hs : s ∉ PairedRange a u v) :
    ((RubikBand.wordPerm w * slabPerm u v * (RubikBand.wordPerm w)⁻¹) *
      (RubikBand.wordPerm z * slabPerm u v * (RubikBand.wordPerm z)⁻¹)⁻¹) s = s := by
  have common (ms : List (Move n)) (hm : RubikBand.StrictControl a ms)
      (t : Sticker n) (ht : t ∉ PairedRange a u v) :
      (RubikBand.wordPerm ms * slabPerm u v * (RubikBand.wordPerm ms)⁻¹) t = slabPerm u v t := by
    apply RubikBand.conjugationOutside a ms hm 2 (slabDepths u v) t
    rintro ⟨ha,hy⟩
    apply ht
    apply (paired_range_iff a u v h t).mpr
    exact ⟨ha,(slab_bands_iff u v t).mp hy⟩
  have brange (t : Sticker n) : slabPerm u v t ∈ PairedRange a u v ↔ t ∈ PairedRange a u v := by
    rw [paired_range_iff a u v h,paired_range_iff a u v h]
    have hy : ColumnBand u v (slabPerm u v t) ↔ ColumnBand u v t := by
      constructor
      · rintro ⟨d,hd,hb⟩
        exact ⟨d,hd,(RubikBand.baselineBand d 2 (slabDepths u v) t).mp hb⟩
      · rintro ⟨d,hd,hb⟩
        exact ⟨d,hd,(RubikBand.baselineBand d 2 (slabDepths u v) t).mpr hb⟩
    exact and_congr (RubikBand.baselineBand a 2 (slabDepths u v) t) hy
  let t := (slabPerm u v)⁻¹ s
  have ht : t ∉ PairedRange a u v := by
    intro hin
    apply hs
    have ho := (brange t).mpr hin
    simpa [t] using ho
  have hzval : (RubikBand.wordPerm z * slabPerm u v * (RubikBand.wordPerm z)⁻¹) t = s := by
    rw [common z hz t ht]
    simp [t]
  have hzinv : (RubikBand.wordPerm z * slabPerm u v * (RubikBand.wordPerm z)⁻¹)⁻¹ s = t :=
    Equiv.Perm.inv_eq_iff_eq.mpr hzval.symm
  change (RubikBand.wordPerm w * slabPerm u v * (RubikBand.wordPerm w)⁻¹)
    ((RubikBand.wordPerm z * slabPerm u v * (RubikBand.wordPerm z)⁻¹)⁻¹ s) = s
  rw [hzinv,common w hw t ht]
  simp [t]
