import RubikSTM.Proofs.OBTM.Band.RowFaceMinus3
import RubikSTM.Definitions.OBTM.Band.SlabWord
set_option autoImplicit false
open Rubik RubikConstruction.Control RubikOBTM.Band

theorem RubikOBTM.Band.row_face_minus_3 :
    ∀ {n : ℕ} (a d : Fin n)
    (ha : 1 ≤ a.val) (hd : 1 ≤ d.val) (has : 2*a.val+2 ≤ n)
    (hds : 2*d.val+2 ≤ n) (had : a ≠ d) (j : Fin 24), physicalAtom a (Sum.inl (3 : Fin 6)) (minus a d j) = minus a d (finiteAtom (Sum.inl (3 : Fin 6)) j) :=
  @proof_RubikOBTM_Band_row_face_minus_3
