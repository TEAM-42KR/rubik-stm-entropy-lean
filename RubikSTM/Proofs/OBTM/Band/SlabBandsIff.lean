import RubikSTM.Definitions.OBTM.Band.SlabWord
set_option autoImplicit false
open Rubik RubikOBTM.Band

theorem proof_RubikOBTM_Band_slab_bands_iff {n : ℕ} (u v : Fin n) (s : Sticker n) :
    RubikBand.Bands (slabDepths u v) s ↔ ColumnBand u v s := by
  constructor
  · rintro ⟨b,hb,hbs⟩
    obtain ⟨d,hd,rfl⟩ := Finset.mem_image.mp hb
    refine ⟨d,⟨(Finset.mem_Icc.mp hd).1,(Finset.mem_Icc.mp hd).2⟩,?_⟩
    simpa only [RubikBand.Band, Fin.rev_rev, or_comm] using hbs
  · rintro ⟨d,hd,hds⟩
    refine ⟨d.rev,Finset.mem_image.mpr ⟨d,Finset.mem_Icc.mpr hd,rfl⟩,?_⟩
    simpa only [RubikBand.Band, Fin.rev_rev, or_comm] using hds
