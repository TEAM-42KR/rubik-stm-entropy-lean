import RubikSTM.Definitions.Wings.SolverWord
set_option autoImplicit false
open Rubik RubikWing
set_option linter.unusedSimpArgs false

 theorem RubikWing.token_move_correct {n : ℕ} (c : Fin n) (t : Token) :
    movePermutation (tokenMove c t) =
      if t.2 then physicalAtom c t.1 else (physicalAtom c t.1)⁻¹ := by
  have hbase (a : Alphabet) : physicalAtom c a =
      sliceQuarter n (baseMove c a).1 (baseMove c a).2.1 := by
    cases a with
    | inl f => fin_cases f <;> rfl
    | inr f => fin_cases f <;> rfl
  rcases t with ⟨a,b⟩
  cases b with
  | false =>
    change (sliceQuarter n (baseMove c a).1 (baseMove c a).2.1) ^ 3 = (physicalAtom c a)⁻¹
    rw [hbase]
    apply mul_eq_one_iff_eq_inv.mp
    rw [← pow_succ, sliceQuarter_order_four]
  | true =>
    change (sliceQuarter n (baseMove c a).1 (baseMove c a).2.1) ^ 1 = physicalAtom c a
    rw [pow_one, hbase]

 theorem RubikWing.decode_eval {n : ℕ} (c : Fin n) (ts : List Token) :
    RubikBand.wordPerm (decode c ts) = physicalEval c (FreeGroup.mk ts) := by
  simp only [decode, RubikBand.wordPerm, List.map_reverse, List.reverse_reverse,
    List.map_map, physicalEval, FreeGroup.lift_mk]
  congr 1
  apply List.map_congr_left
  intro t _
  rw [Function.comp_apply, token_move_correct]
  cases t.2 <;> rfl

 theorem RubikWing.decode_deletion {n : ℕ} {c : Fin n} (hc : Admissible n c)
    (ts : List Token) :
    RubikBand.wordPerm (RubikBand.faceDeletion c (decode c ts)) =
      faceOnlyEval c (FreeGroup.mk ts) := by
  have hn := c.isLt
  have hlo := hc.one_le
  have hsmall := hc.small
  have hface (f : Fin 6) : (faceMove c f).2.1 ≠ c ∧ (faceMove c f).2.1 ≠ c.rev := by
    fin_cases f <;> constructor <;> intro he <;>
      have hv := congrArg Fin.val he <;> simp [faceMove, lo, hi, Fin.rev] at hv <;> omega
  have hsingle (t : Token) :
      RubikBand.wordPerm (RubikBand.faceDeletion c (decode c [t])) =
        faceOnlyEval c (FreeGroup.mk [t]) := by
    rcases t with ⟨a,b⟩
    cases a with
    | inl f =>
      have hf : RubikBand.faceDeletion c (decode c [(Sum.inl f,b)]) =
          [tokenMove c (Sum.inl f,b)] := by
        simp [RubikBand.faceDeletion, decode, tokenMove, baseMove, (hface f).1, (hface f).2]
      rw [hf]
      change movePermutation (tokenMove c (Sum.inl f,b)) * 1 = _
      rw [mul_one, token_move_correct]
      cases b <;> simp [faceOnlyEval, faceEval, deletion, FreeGroup.lift_mk, physicalAtom]
    | inr f =>
      have hf : RubikBand.faceDeletion c (decode c [(Sum.inr f,b)]) = [] := by
        fin_cases f <;> simp [RubikBand.faceDeletion, decode, tokenMove, baseMove, sliceMove]
      rw [hf]
      cases b <;> simp [RubikBand.wordPerm, faceOnlyEval, faceEval, deletion, FreeGroup.lift_mk]
  have happ (u v : List (Move n)) : RubikBand.wordPerm (u ++ v) =
      RubikBand.wordPerm v * RubikBand.wordPerm u := by
    simp [RubikBand.wordPerm, List.reverse_append, List.prod_append]
  have hfilter (u v : List (Move n)) : RubikBand.faceDeletion c (u ++ v) =
      RubikBand.faceDeletion c u ++ RubikBand.faceDeletion c v := by
    simp [RubikBand.faceDeletion]
  induction ts with
  | nil => simp [decode, RubikBand.faceDeletion, RubikBand.wordPerm, ← FreeGroup.one_eq_mk]
  | cons t ts ih =>
    have hd : decode c (t :: ts) = decode c ts ++ decode c [t] := by simp [decode]
    have hmk : FreeGroup.mk (t :: ts) = FreeGroup.mk [t] * FreeGroup.mk ts := by
      rw [FreeGroup.mul_mk]; rfl
    rw [hd, hfilter, happ, ih, hsingle, hmk, map_mul]

 theorem RubikWing.decode_allowed {n : ℕ} (c : Fin n) (ts : List Token) :
    RubikBand.AllowedControl c (decode c ts) := by
  intro m hm
  obtain ⟨⟨a,b⟩, ht, rfl⟩ := List.mem_map.mp hm
  cases a with
  | inl f => fin_cases f <;> simp [tokenMove, baseMove, faceMove, lo, hi]
  | inr f => fin_cases f <;> simp [tokenMove, baseMove, sliceMove]

 theorem RubikWing.uniform_cleanup {n : ℕ} {c : Fin n} (hc : Admissible n c)
    (σ : Equiv.Perm Label) :
    (solverWord c σ).length ≤ uniformCost ∧
    RubikBand.StrictControl c (solverWord c σ) ∧
    (∀ i b, RubikBand.wordPerm (solverWord c σ) (lab c i b) = lab c (σ i) b) ∧
    (∀ s : Sticker n, ¬ RubikBand.Band c s → RubikBand.wordPerm (solverWord c σ) s = s) := by
  have hspec : finiteEval (solver σ) = σ ∧ deletion (solver σ) = 1 :=
    Classical.choose_spec (strict_finite_realization σ)
  have hstrict : RubikBand.StrictControl c (solverWord c σ) := by
    refine ⟨decode_allowed c _, ?_⟩
    rw [solverWord, decode_deletion hc, solverTokens, FreeGroup.mk_toWord]
    change faceEval c (deletion (solver σ)) = 1
    rw [hspec.2, map_one]
  refine ⟨?_, hstrict, ?_, ?_⟩
  · change (decode c (solverTokens σ)).length ≤ uniformCost
    simp only [decode, List.length_map, List.length_reverse]
    exact Finset.le_sup (f := fun σ : Equiv.Perm Label => (solverTokens σ).length) (Finset.mem_univ σ)
  · intro i b
    rw [solverWord, decode_eval, solverTokens, FreeGroup.mk_toWord, word_action hc, hspec.1]
  · intro s hs
    exact RubikBand.strictOutside c (solverWord c σ) hstrict s hs

namespace RubikWing

def IsWing {n : ℕ} (c : Fin n) (s : Sticker n) : Prop :=
  ∃ a : Axis, (coordinate s.val.1 a = c ∨ coordinate s.val.1 a = c.rev) ∧
    ∀ b : Axis, b ≠ a → (coordinate s.val.1 b).val = 0 ∨ (coordinate s.val.1 b).val = n-1

def IsCorner {n : ℕ} (s : Sticker n) : Prop :=
  ∀ a : Axis, (coordinate s.val.1 a).val = 0 ∨ (coordinate s.val.1 a).val = n-1

def IsMiddleSkeleton {n : ℕ} (s : Sticker n) : Prop :=
  ∀ a : Axis, (coordinate s.val.1 a).val = 0 ∨ (coordinate s.val.1 a).val = n-1 ∨
    2 * (coordinate s.val.1 a).val = n-1
end RubikWing
