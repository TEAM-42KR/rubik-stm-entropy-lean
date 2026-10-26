import RubikSTM.Definitions.Surface.GenericRange
set_option autoImplicit false
open Rubik RubikGeometry RubikGlobal
open scoped Classical

open RubikCore
private theorem RubikCore.isLevel_rev {n : ℕ} (x : Fin n) : IsLevel x.rev ↔ IsLevel x := by
  have h {y : Fin n} : IsLevel y → IsLevel y.rev := by
    intro hy
    rcases hy with h0 | h1 | hm
    · right; left
      simp [Fin.rev, h0]
    · left
      simp only [Fin.rev, h1]
      omega
    · right; right
      rw [Fin.rev_rev]
      exact hm.symm
  exact ⟨fun hh => by simpa using h hh, h⟩

private theorem RubikGlobal.depths_generic_lab {n : ℕ} {a b : Fin n} (hg : Generic n a b) (i : Fin 24) :
    RubikGlobal.depths (lab a b i).val = (a.val, b.val) := by
  have ha := hg.a_small
  have hb := hg.b_small
  have hal : 2 * a.val < n := by omega
  have hbl : 2 * b.val < n := by omega
  have har : ¬2 * (n - (a.val + 1)) < n := by omega
  have hbr : ¬2 * (n - (b.val + 1)) < n := by omega
  fin_cases i <;> simp [RubikGlobal.depths, RubikGlobal.tangent, lab, rawLab, posTable, normalTable,
    hal, hbl, har, hbr]

private theorem RubikGlobal.generic_label_parameters {n : ℕ} {a b a' b' : Fin n} (hg : Generic n a b) (hg' : Generic n a' b')
    {i j : Fin 24} (h : lab a b i = lab a' b' j) : a = a' ∧ b = b' := by
  have hh := congrArg (fun s : Sticker n => RubikGlobal.depths s.val) h
  simp only [RubikGlobal.depths_generic_lab hg, RubikGlobal.depths_generic_lab hg'] at hh
  exact ⟨Fin.ext (congrArg Prod.fst hh), Fin.ext (congrArg Prod.snd hh)⟩

private theorem RubikGlobal.index_generic {n : ℕ} (p : RubikGlobal.Q n) :
    Generic n (RubikGlobal.depth p.val.1) (RubikGlobal.depth p.val.2) := by
  constructor
  · change 1 ≤ p.val.1.val + 1; omega
  · change 1 ≤ p.val.2.val + 1; omega
  · have := p.val.1.isLt
    change 2 * (p.val.1.val + 1) + 2 ≤ n
    omega
  · have := p.val.2.isLt
    change 2 * (p.val.2.val + 1) + 2 ≤ n
    omega
  · intro h
    apply p.property
    apply Fin.ext
    have hv := congrArg Fin.val h
    change p.val.1.val + 1 = p.val.2.val + 1 at hv
    omega

theorem proof_RubikGlobal_generic_ranges_disjoint {n : ℕ} (p q : RubikGlobal.Q n) (hpq : p ≠ q) :
    Disjoint (RubikGlobal.GenericRange p) (RubikGlobal.GenericRange q) := by
  apply Set.disjoint_left.mpr
  rintro s ⟨i, hi⟩ ⟨j, hj⟩
  have h : RubikGlobal.label p i = RubikGlobal.label q j := hi.trans hj.symm
  obtain ⟨ha,hb⟩ := RubikGlobal.generic_label_parameters
    (RubikGlobal.index_generic p) (RubikGlobal.index_generic q) h
  apply hpq
  apply Subtype.ext
  apply Prod.ext
  · apply Fin.ext
    have hv := congrArg Fin.val ha
    change p.val.1.val + 1 = q.val.1.val + 1 at hv
    omega
  · apply Fin.ext
    have hv := congrArg Fin.val hb
    change p.val.2.val + 1 = q.val.2.val + 1 at hv
    omega

#print axioms proof_RubikGlobal_generic_ranges_disjoint
