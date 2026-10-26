import Mathlib
set_option autoImplicit false

theorem proof_RubikCore_finite_word_compression {M X : Type*} [Fintype X] (step : X → M → X) (x y : X)
    (h : ∃ w : List M, w.foldl step x = y) :
    ∃ w : List M, w.length < Fintype.card X ∧ w.foldl step x = y := by
  classical
  have hex : ∃ k : ℕ, ∃ w : List M, w.length = k ∧ w.foldl step x = y := by
    obtain ⟨w, hw⟩ := h
    exact ⟨w.length, w, rfl, hw⟩
  obtain ⟨w, hlen, hw⟩ := Nat.find_spec hex
  have hmin (v : List M) (hv : v.foldl step x = y) : w.length ≤ v.length := by
    rw [hlen]
    exact Nat.find_min' hex ⟨v, rfl, hv⟩
  refine ⟨w, ?_, hw⟩
  by_contra hc
  let f : Fin (w.length + 1) → X := fun i => (w.take i.val).foldl step x
  have hn : ¬ Function.Injective f := Fintype.not_injective_of_card_lt f (by
    simp only [Fintype.card_fin]
    omega)
  obtain ⟨i, j, heq, hne⟩ := Function.not_injective_iff.mp hn
  have hneval : i.val ≠ j.val := fun hval => hne (Fin.ext hval)
  have hdup : ∃ i j : Fin (w.length + 1), i.val < j.val ∧ f i = f j := by
    rcases lt_or_gt_of_ne hneval with hij | hji
    · exact ⟨i, j, hij, heq⟩
    · exact ⟨j, i, hji, heq.symm⟩
  obtain ⟨i, j, hij, heq⟩ := hdup
  let v := w.take i.val ++ w.drop j.val
  have hv : v.foldl step x = y := by
    change (w.take i.val ++ w.drop j.val).foldl step x = y
    rw [List.foldl_append]
    change (w.drop j.val).foldl step (f i) = y
    rw [heq]
    change (w.drop j.val).foldl step ((w.take j.val).foldl step x) = y
    rw [← List.foldl_append, List.take_append_drop]
    exact hw
  have hvlen : v.length < w.length := by
    dsimp [v]
    simp only [List.length_append, List.length_take, List.length_drop]
    have hi := i.isLt
    have hj := j.isLt
    omega
  exact (Nat.not_le_of_lt hvlen) (hmin v hv)

#print axioms proof_RubikCore_finite_word_compression
