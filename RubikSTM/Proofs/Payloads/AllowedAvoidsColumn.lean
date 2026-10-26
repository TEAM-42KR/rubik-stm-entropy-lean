import Mathlib
import RubikSTM.Definitions.Payloads.Realizes
set_option autoImplicit false

theorem proof_RubikPayload_allowedAvoidsColumn {n : ℕ} {a b : Fin n} (hg : RubikGeometry.Generic n a b)
  (w : List (Rubik.Move n)) (hw : RubikBand.AllowedControl a w) :
  ∀ m ∈ w, m.2.1 ≠ b ∧ m.2.1 ≠ b.rev := by
  have ha := hg.one_le_a
  have hb := hg.one_le_b
  have has := hg.a_small
  have hbs := hg.b_small
  have hab : a.val ≠ b.val := by intro h; exact hg.ne (Fin.ext h)
  intro m hm
  have hvalues : m.2.1.val = 0 ∨ m.2.1.val = n-1 ∨
      m.2.1.val = a.val ∨ m.2.1.val = n-(a.val+1) := by
    rcases hw m hm with h | h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl (congrArg Fin.val h)))
    · exact Or.inr (Or.inr (Or.inr (congrArg Fin.val h)))
  have hmb : m.2.1.val ≠ b.val := by rcases hvalues with h | h | h | h <;> omega
  have hmbr : m.2.1.val ≠ n-(b.val+1) := by rcases hvalues with h | h | h | h <;> omega
  exact ⟨fun he => hmb (congrArg Fin.val he), fun he => hmbr (congrArg Fin.val he)⟩

#print axioms proof_RubikPayload_allowedAvoidsColumn
