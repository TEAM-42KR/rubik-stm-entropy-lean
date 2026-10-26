import Mathlib
import RubikSTM.Definitions.Payloads.Realizes
import RubikSTM.Lemmas.Payloads.AdmissibleGeneric
import RubikSTM.Lemmas.Payloads.LabelOutsideThirdBand
import RubikSTM.Lemmas.Payloads.SingleIndexWordAction
import RubikSTM.Lemmas.Orbits.FlipLabel
import RubikSTM.Definitions.Wings.SolverWord
set_option autoImplicit false

theorem proof_RubikPayload_rowFamily {n : ℕ} {A Y : Finset (Fin n)} (h : RubikPayload.Admissible A Y)
  (K : ℕ) (σ : Fin n → Equiv.Perm (Fin 24)) (ws : Fin n → List (Rubik.Move n))
  (hcost : ∀ a ∈ A, (ws a).length ≤ K)
  (hstrict : ∀ a ∈ A, RubikBand.StrictControl a (ws a))
  (hact : ∀ a ∈ A, ∀ b ∈ Y, ∀ hb : 0 < b.val ∧ b.val + 1 < n, ∀ i,
    RubikBand.wordPerm (ws a) (RubikGeometry.lab a b i) = RubikGeometry.lab a b (σ a i) ∧
    RubikBand.wordPerm (ws a) (RubikOrbit.minusLab a b hb i) =
      RubikOrbit.minusLab a b hb (σ a i)) :
  let U := (A.sort (· ≤ ·)).flatMap ws
  U.length ≤ A.card * K ∧
  (∀ s : Rubik.Sticker n, ¬ RubikBand.Bands A s → RubikBand.wordPerm U s = s) ∧
  (∀ a ∈ A, ∀ b ∈ Y, ∀ hb : 0 < b.val ∧ b.val + 1 < n, ∀ i,
    RubikBand.wordPerm U (RubikGeometry.lab a b i) = RubikGeometry.lab a b (σ a i) ∧
    RubikBand.wordPerm U (RubikOrbit.minusLab a b hb i) =
      RubikOrbit.minusLab a b hb (σ a i)) := by
  have cat (u v : List (Rubik.Move n)) : RubikBand.wordPerm (u++v) =
      RubikBand.wordPerm v * RubikBand.wordPerm u := by
    simp [RubikBand.wordPerm, List.reverse_append]
  have Hlen : ∀ rows : List (Fin n), (∀ c ∈ rows, (ws c).length ≤ K) →
      (rows.flatMap ws).length ≤ rows.length * K := by
    intro rows
    induction rows with
    | nil => intro hc; simp
    | cons c rows ih =>
      intro hc
      simp only [List.flatMap_cons, List.length_append, List.length_cons]
      calc
        (ws c).length + (rows.flatMap ws).length ≤ K + rows.length * K :=
          Nat.add_le_add (hc c (by simp)) (ih (by intro d hd; exact hc d (by simp [hd])))
        _ = (rows.length+1)*K := by simp [Nat.add_mul, Nat.add_comm]
  have Hfix : ∀ s : Rubik.Sticker n, ¬ RubikBand.Bands A s →
      RubikBand.wordPerm ((A.sort (· ≤ ·)).flatMap ws) s = s := by
    intro s hs
    have H : ∀ rows : List (Fin n), (∀ c ∈ rows, c ∈ A) →
        RubikBand.wordPerm (rows.flatMap ws) s = s := by
      intro rows
      induction rows with
      | nil => intro hc; rfl
      | cons c rows ih =>
        intro hc
        have hcs : ¬ RubikBand.Band c s := by intro hb; exact hs ⟨c,hc c (by simp),hb⟩
        have hf := RubikBand.strictOutside c (ws c) (hstrict c (hc c (by simp))) s hcs
        rw [List.flatMap_cons, cat, Equiv.Perm.mul_apply, hf]
        exact ih (by intro d hd; exact hc d (by simp [hd]))
    exact H _ (by intro c hc; simpa using hc)
  refine ⟨?_, Hfix, ?_⟩
  · simpa using Hlen (A.sort (· ≤ ·)) (by intro c hc; exact hcost c (by simpa using hc))
  · intro a ha b hbY hb i
    have hg := RubikPayload.admissibleGeneric h ha hbY
    have hgs : RubikGeometry.Generic n b a := ⟨hg.one_le_b,hg.one_le_a,hg.b_small,hg.a_small,Ne.symm hg.ne⟩
    have Hstep : ∀ c ∈ A, ∀ i,
        RubikBand.wordPerm (ws c) (RubikGeometry.lab a b i) =
          RubikGeometry.lab a b (if c=a then σ a i else i) ∧
        RubikBand.wordPerm (ws c) (RubikOrbit.minusLab a b hb i) =
          RubikOrbit.minusLab a b hb (if c=a then σ a i else i) := by
      intro c hc j
      by_cases he : c=a
      · subst c
        simpa using hact a ha b hbY hb j
      · have hcb : c ≠ b := by
          intro heq
          exact Finset.disjoint_left.mp h.2.2 hc (heq.symm ▸ hbY)
        have hp := RubikPayload.labelOutsideThirdBand hg (h.1 c hc) he hcb j
        have hm : ¬ RubikBand.Band c (RubikOrbit.minusLab a b hb j) := by
          rw [RubikOrbit.flipLabel hg hb]
          exact RubikPayload.labelOutsideThirdBand hgs (h.1 c hc) hcb he _
        simpa only [he, if_false] using
          And.intro (RubikBand.strictOutside c (ws c) (hstrict c hc) _ hp)
            (RubikBand.strictOutside c (ws c) (hstrict c hc) _ hm)
    have hp := RubikPayload.singleIndexWordAction (A.sort (· ≤ ·)) (Finset.sort_nodup _ _)
      a ws (RubikGeometry.lab a b) (σ a) (by
        intro c hc j; exact (Hstep c (by simpa using hc) j).1) i
    have hm := RubikPayload.singleIndexWordAction (A.sort (· ≤ ·)) (Finset.sort_nodup _ _)
      a ws (RubikOrbit.minusLab a b hb) (σ a) (by
        intro c hc j; exact (Hstep c (by simpa using hc) j).2) i
    exact ⟨by simpa [ha] using hp, by simpa [ha] using hm⟩

#print axioms proof_RubikPayload_rowFamily
