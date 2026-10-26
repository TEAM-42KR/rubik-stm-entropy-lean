import RubikSTM.Definitions.OBTM.Band.CleanAction
import RubikSTM.Lemmas.Construction.Control.Physical.ChronologicalAlgebra
set_option autoImplicit false
open Rubik RubikConstruction.Control RubikConstruction.Control.Physical RubikOBTM.Band

theorem proof_RubikOBTM_Band_physical_control_strict {n : ℕ} (a : Fin n)
    (ha : 1 ≤ a.val) (has : 2*a.val+2 ≤ n) (ms : List (Move n))
    (hm : ∀ m ∈ ms, Allowed a m) (hd : chronological (faceOnlyMoves a ms) = 1) :
    RubikBand.StrictControl a ms := by
  have han := a.isLt
  have hla : low a ≠ a := by intro h; have := congrArg Fin.val h; simp only [low,Fin.val_mk] at this; omega
  have hlar : low a ≠ a.rev := by intro h; have := congrArg Fin.val h; simp only [low,Fin.rev,Fin.val_mk] at this; omega
  have hha : high a ≠ a := by intro h; have := congrArg Fin.val h; simp only [high,Fin.val_mk] at this; omega
  have hhar : high a ≠ a.rev := by intro h; have := congrArg Fin.val h; simp only [high,Fin.rev,Fin.val_mk] at this; omega
  refine ⟨?_,?_⟩
  · intro m hh
    rcases hm m hh with h|h|h
    · exact Or.inl (by simpa [low] using congrArg Fin.val h)
    · exact Or.inr (Or.inl (by simpa [high] using congrArg Fin.val h))
    · exact Or.inr (Or.inr (Or.inl h))
  · have he : RubikBand.faceDeletion a ms = faceOnlyMoves a ms := by
      unfold RubikBand.faceDeletion faceOnlyMoves
      apply List.filter_congr
      intro m hh
      rcases hm m hh with h|h|h
      · simp [h,hla,hlar]
      · simp [h,hha,hhar]
      · simp [h,Ne.symm hla,Ne.symm hha]
    rw [he]
    rw [chronological_algebra] at hd
    simpa [RubikBand.wordPerm,List.map_reverse] using hd
