import Mathlib
set_option autoImplicit false

namespace RubikCodebook.Conditional

def coordinateEquiv {L M : ℕ} (a b : Fin L → Fin M) :
    {p : Fin L × Fin M // p.2 = a p.1 ∨ p.2 = b p.1} ≃
      ({i : Fin L // a i = b i} ⊕
        ({i : Fin L // a i ≠ b i} ⊕ {i : Fin L // a i ≠ b i})) where
  toFun p := by
    classical
    by_cases ha : p.val.2 = a p.val.1
    · by_cases he : a p.val.1 = b p.val.1
      · exact Sum.inl ⟨p.val.1, he⟩
      · exact Sum.inr (Sum.inl ⟨p.val.1, he⟩)
    · exact Sum.inr (Sum.inr ⟨p.val.1, by
        intro he
        exact ha ((p.property.resolve_left ha).trans he.symm)⟩)
  invFun p := match p with
    | Sum.inl i => ⟨(i.val, a i.val), Or.inl rfl⟩
    | Sum.inr (Sum.inl i) => ⟨(i.val, a i.val), Or.inl rfl⟩
    | Sum.inr (Sum.inr i) => ⟨(i.val, b i.val), Or.inr rfl⟩
  left_inv p := by
    classical
    rcases p with ⟨⟨i, m⟩, hp⟩
    dsimp
    split_ifs with ha he
    · apply Subtype.ext
      exact Prod.ext rfl ha.symm
    · apply Subtype.ext
      exact Prod.ext rfl ha.symm
    · apply Subtype.ext
      exact Prod.ext rfl (hp.resolve_left ha).symm
  right_inv p := by
    classical
    rcases p with i | (i | i)
    · simp [i.property]
    · simp [i.property]
    · simp [Ne.symm i.property]

def complete {L M : ℕ} (a b : Fin L → Fin M) {E : Type*}
    (s : {i : Fin L // a i = b i} → E)
    (u : {i : Fin L // a i ≠ b i} → E) (i : Fin L) : E := by
  classical
  exact if h : a i = b i then s ⟨i, h⟩ else u ⟨i, h⟩

def sampleEquiv {L M : ℕ} (a b : Fin L → Fin M) (E : Type*) :
    ({p : Fin L × Fin M // p.2 = a p.1 ∨ p.2 = b p.1} → E) ≃
      (({i : Fin L // a i = b i} → E) ×
        ({i : Fin L // a i ≠ b i} → E) × ({i : Fin L // a i ≠ b i} → E)) :=
  (Equiv.arrowCongr (coordinateEquiv a b) (Equiv.refl E)).trans
    ((Equiv.sumArrowEquivProdArrow _ _ E).trans
      (Equiv.prodCongr (Equiv.refl _) (Equiv.sumArrowEquivProdArrow _ _ E)))

end RubikCodebook.Conditional

#print axioms RubikCodebook.Conditional.coordinateEquiv
#print axioms RubikCodebook.Conditional.sampleEquiv
