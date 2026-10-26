import RubikSTM.Definitions.OBTM.Band.SlabWord
import RubikSTM.Lemmas.OBTM.Band.RowFaceMinus0
import RubikSTM.Lemmas.OBTM.Band.RowFaceMinus1
import RubikSTM.Lemmas.OBTM.Band.RowFaceMinus2
import RubikSTM.Lemmas.OBTM.Band.RowFaceMinus3
import RubikSTM.Lemmas.OBTM.Band.RowFaceMinus4
import RubikSTM.Lemmas.OBTM.Band.RowFaceMinus5
set_option autoImplicit false
open Rubik RubikConstruction.Control RubikOBTM.Band
theorem proof_RubikOBTM_Band_row_face_minus {n : ℕ} (a d : Fin n)
    (ha : 1 ≤ a.val) (hd : 1 ≤ d.val) (has : 2*a.val+2 ≤ n)
    (hds : 2*d.val+2 ≤ n) (had : a ≠ d) (f : Fin 6) (j : Fin 24) :
    physicalAtom a (Sum.inl f) (minus a d j) = minus a d (finiteAtom (Sum.inl f) j) := by
  fin_cases f
  · exact row_face_minus_0 a d ha hd has hds had j
  · exact row_face_minus_1 a d ha hd has hds had j
  · exact row_face_minus_2 a d ha hd has hds had j
  · exact row_face_minus_3 a d ha hd has hds had j
  · exact row_face_minus_4 a d ha hd has hds had j
  · exact row_face_minus_5 a d ha hd has hds had j
