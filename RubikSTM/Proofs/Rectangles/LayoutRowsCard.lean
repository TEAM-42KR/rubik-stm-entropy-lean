import RubikSTM.Definitions.Rectangles.Layout
set_option autoImplicit false

open RubikRectangle

theorem proof_RubikRectangle_layout_rows_card {n k : ℕ} {X : Finset (Fin n)} (P : Layout X k) (j : Fin P.blocks) :
    (P.rows j).card ≤ k := by
  classical
  have h := Finset.card_le_card_of_injOn P.row
    (s := P.rows j) (t := Finset.univ) (by intro a ha; exact Finset.mem_univ _)
    (by
      intro a ha b hb he
      have hA := Finset.mem_filter.mp ha
      have hB := Finset.mem_filter.mp hb
      exact P.injective a hA.1 b hB.1 (hA.2.trans hB.2.symm) he)
  simpa using h

#print axioms proof_RubikRectangle_layout_rows_card
