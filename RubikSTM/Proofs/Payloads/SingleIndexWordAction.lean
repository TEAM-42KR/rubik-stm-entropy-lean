import Mathlib
import RubikSTM.Definitions.Payloads.Realizes
set_option autoImplicit false

theorem proof_RubikPayload_singleIndexWordAction {n : ℕ} {I : Type*} [DecidableEq I] (rows : List I)
  (hnd : rows.Nodup) (a : I) (ws : I → List (Rubik.Move n))
  (lab : Fin 24 → Rubik.Sticker n) (σ : Equiv.Perm (Fin 24))
  (hstep : ∀ c ∈ rows, ∀ i, RubikBand.wordPerm (ws c) (lab i) =
    lab (if c = a then σ i else i)) :
  ∀ i, RubikBand.wordPerm (rows.flatMap ws) (lab i) =
    lab (if a ∈ rows then σ i else i) := by
  have cat (u v : List (Rubik.Move n)) : RubikBand.wordPerm (u++v) =
      RubikBand.wordPerm v * RubikBand.wordPerm u := by
    simp [RubikBand.wordPerm, List.reverse_append]
  revert hnd hstep
  induction rows with
  | nil => intro hnd hstep i; simp [RubikBand.wordPerm]
  | cons c rows ih =>
    intro hnd hstep i
    have ht := ih (List.nodup_cons.mp hnd).2 (by
      intro d hd j
      exact hstep d (by simp [hd]) j)
    rw [List.flatMap_cons, cat, Equiv.Perm.mul_apply, hstep c (by simp)]
    by_cases hc : c = a
    · subst c
      have hn : a ∉ rows := (List.nodup_cons.mp hnd).1
      simpa [hn] using ht (σ i)
    · simpa [hc, Ne.symm hc] using ht i

#print axioms proof_RubikPayload_singleIndexWordAction
