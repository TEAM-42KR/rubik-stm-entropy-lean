import Mathlib
set_option autoImplicit false

theorem proof_RubikCompiler_concatenateWords {M X : Type*} (move : M → Equiv.Perm X)
  (ws : List (List M)) (b : ℕ) (hcost : ∀ w ∈ ws, w.length ≤ b) :
  ((ws.flatten.map move).reverse.prod =
      (ws.map (fun w => (w.map move).reverse.prod)).reverse.prod) ∧
    ws.flatten.length = (ws.map List.length).sum ∧
    ws.flatten.length ≤ ws.length * b := by
  have hreal : (ws.flatten.map move).reverse.prod =
      (ws.map (fun w => (w.map move).reverse.prod)).reverse.prod := by
    clear hcost
    induction ws with
    | nil => simp
    | cons w ws ih =>
      simp only [List.flatten_cons, List.map_append, List.reverse_append,
        List.prod_append, List.map_cons, List.reverse_cons, List.prod_singleton]
      rw [ih]
  refine ⟨hreal, ?_⟩
  clear hreal
  revert hcost
  induction ws with
  | nil => simp
  | cons w ws ih =>
    intro hc
    have hcw : w.length ≤ b := hc w (by simp)
    have iht := ih (by
      intro v hv
      exact hc v (by simp [hv]))
    simp only [List.flatten_cons, List.length_append, List.map_cons,
      List.sum_cons, List.length_cons]
    constructor
    · rw [iht.1]
    · calc
        w.length + ws.flatten.length ≤ b + ws.length * b := Nat.add_le_add hcw iht.2
        _ = (ws.length + 1) * b := by simp [Nat.add_mul, Nat.add_comm]

#print axioms proof_RubikCompiler_concatenateWords
