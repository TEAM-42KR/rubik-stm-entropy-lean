import Mathlib
import RubikSTM.Definitions.Payloads.Realizes
import RubikSTM.Lemmas.Payloads.ChronologicalWord
import RubikSTM.Lemmas.Construction.Control.Physical.ActualMovesAllowed
import RubikSTM.Lemmas.Construction.Control.Physical.ActualMovesDeletion
set_option autoImplicit false

theorem proof_RubikPayload_signedStrict {n : ℕ} (a : Fin n) (ha : RubikPayload.Half a)
  (letters : List RubikConstruction.Control.Physical.SignedLetter)
  (hd : RubikConstruction.Control.deletion (FreeGroup.mk letters) = 1) :
  RubikBand.StrictControl a (RubikConstruction.Control.Physical.actualMoves a letters) := by
  have hlow : RubikConstruction.Control.low a ≠ a := by
    intro h; have hh := congrArg Fin.val h
    change 0 = a.val at hh; have := ha.1; omega
  have hhigh : RubikConstruction.Control.high a ≠ a := by
    intro h; have hh := congrArg Fin.val h
    change n-1 = a.val at hh; have := ha.1; have := ha.2; omega
  have hlowr : RubikConstruction.Control.low a ≠ a.rev := by
    intro h; have hh := congrArg Fin.val h
    change 0 = n-(a.val+1) at hh; have := ha.2; omega
  have hhighr : RubikConstruction.Control.high a ≠ a.rev := by
    intro h; have hh := congrArg Fin.val h
    change n-1 = n-(a.val+1) at hh; have := ha.1; have := ha.2; omega
  have hfilters : RubikBand.faceDeletion a (RubikConstruction.Control.Physical.actualMoves a letters) =
      RubikConstruction.Control.Physical.faceOnlyMoves a (RubikConstruction.Control.Physical.actualMoves a letters) := by
    unfold RubikBand.faceDeletion RubikConstruction.Control.Physical.faceOnlyMoves
    apply List.filter_congr
    intro m hm
    have hmA := RubikConstruction.Control.Physical.actual_moves_allowed a letters m hm
    rcases hmA with h | h | h
    · simp [h, hlow, hlowr]
    · simp [h, hhigh, hhighr]
    · simp [h, Ne.symm hlow, Ne.symm hhigh]
  constructor
  · intro m hm
    rcases RubikConstruction.Control.Physical.actual_moves_allowed a letters m hm with h | h | h
    · exact Or.inl (by simpa only [h, RubikConstruction.Control.low])
    · exact Or.inr (Or.inl (by simpa only [h, RubikConstruction.Control.high]))
    · exact Or.inr (Or.inr (Or.inl h))
  · rw [hfilters, ← RubikPayload.chronologicalWord,
      RubikConstruction.Control.Physical.actual_moves_deletion a ha.1 ha.2]
    simp [RubikConstruction.Control.faceOnlyEval, hd]

#print axioms proof_RubikPayload_signedStrict
