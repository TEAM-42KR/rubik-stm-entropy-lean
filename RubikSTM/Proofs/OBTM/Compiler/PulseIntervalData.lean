import RubikSTM.Definitions.OBTM.Compiler.NativeProgram
import RubikSTM.Lemmas.OBTM.Band.PairedRangeIff
import RubikSTM.Lemmas.Payloads.RectanglesBands
set_option autoImplicit false

theorem proof_RubikOBTMCompiler_pulse_interval_data {n : ℕ} {A Y : Finset (Fin n)} (h : RubikPayload.Admissible A Y)
    (hord : Set.OrdConnected (Y : Set (Fin n))) (hY : Y.Nonempty) :
    (∀ d : Fin n, d ∈ Y ↔ RubikOBTM.Band.InInterval (Y.min' hY) (Y.max' hY) d) ∧
    (∀ a ∈ A, RubikOBTM.Band.Admissible n a (Y.min' hY) (Y.max' hY)) ∧
    (∀ a ∈ A, ∀ s : Rubik.Sticker n,
      s ∈ RubikOBTM.Band.PairedRange a (Y.min' hY) (Y.max' hY) →
      RubikPayload.Rectangles A Y s) := by
  classical
  have hmem (d : Fin n) : d ∈ Y ↔ RubikOBTM.Band.InInterval (Y.min' hY) (Y.max' hY) d := by
    constructor
    · intro hd
      exact ⟨Y.min'_le _ hd, Y.le_max' _ hd⟩
    · intro hd
      exact hord.out (Y.min'_mem hY) (Y.max'_mem hY) hd
  have hadm (a : Fin n) (ha : a ∈ A) :
      RubikOBTM.Band.Admissible n a (Y.min' hY) (Y.max' hY) := by
    have haH := h.1 a ha
    have hlH := h.2.1 _ (Y.min'_mem hY)
    have huH := h.2.1 _ (Y.max'_mem hY)
    have hnot : a ∉ Y := fun hay => Finset.disjoint_left.mp h.2.2 ha hay
    have haout : a.val < (Y.min' hY).val ∨ (Y.max' hY).val < a.val := by
      by_contra hn
      apply hnot
      apply (hmem a).mpr
      dsimp [RubikOBTM.Band.InInterval]
      omega
    exact ⟨haH.1, haH.2, hlH.1, Y.min'_le_max' hY, huH.2, haout⟩
  refine ⟨hmem, hadm, ?_⟩
  intro a ha s hs
  obtain ⟨has, d, hd, hds⟩ := (RubikOBTM.Band.paired_range_iff _ _ _ (hadm a ha) s).mp hs
  apply (RubikPayload.rectanglesBands h s).mpr
  exact ⟨⟨a, ha, has⟩, ⟨d, (hmem d).mpr hd, hds⟩⟩
