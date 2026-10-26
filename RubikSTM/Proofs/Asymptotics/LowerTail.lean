import Mathlib
import RubikSTM.Definitions.Geometry.StmGraph
set_option autoImplicit false

open Rubik

private def RubikGeometry.moveGroup (n : ℕ) : Subgroup (Equiv.Perm (Sticker n)) :=
  Subgroup.closure (Set.range (fun m : Move n => movePermutation m))

section Labels
variable {n : ℕ}

private def RubikGeometry.lo (a : Fin n) : Fin n := ⟨0, by have := a.isLt; omega⟩

private def RubikGeometry.hi (a : Fin n) : Fin n := ⟨n - 1, by have := a.isLt; omega⟩

private structure RubikGeometry.Generic (n : ℕ) (a b : Fin n) : Prop where
  one_le_a : 1 ≤ a.val
  one_le_b : 1 ≤ b.val
  a_small : 2 * a.val + 2 ≤ n
  b_small : 2 * b.val + 2 ≤ n
  ne : a ≠ b

private def RubikGeometry.posTable (a b : Fin n) : Fin 24 → Coord n :=
  ![(hi a, b.rev, a),
    (hi a, b, a.rev),
    (hi a, a.rev, b.rev),
    (hi a, a, b),
    (a, hi a, b.rev),
    (a, b, hi a),
    (b.rev, a, hi a),
    (a.rev, b.rev, hi a),
    (b, a.rev, hi a),
    (b, lo a, a.rev),
    (lo a, b.rev, a.rev),
    (lo a, b, a),
    (b.rev, hi a, a.rev),
    (a.rev, hi a, b),
    (b, hi a, a),
    (lo a, a, b.rev),
    (lo a, a.rev, b),
    (a.rev, lo a, b.rev),
    (b.rev, lo a, a),
    (a, lo a, b),
    (b, a, lo a),
    (a.rev, b, lo a),
    (b.rev, a.rev, lo a),
    (a, b.rev, lo a)]

private def RubikGeometry.normalTable : Fin 24 → Normal :=
  ![(0, true), (0, true), (0, true), (0, true), (1, true), (2, true), (2, true), (2, true), (2, true), (1, false), (0, false), (0, false), (1, true), (1, true), (1, true), (0, false), (0, false), (1, false), (1, false), (1, false), (2, false), (2, false), (2, false), (2, false)]

private def RubikGeometry.rawLab (a b : Fin n) (i : Fin 24) : RawSticker n := (posTable a b i, normalTable i)

private theorem RubikGeometry.rawLab_isSurface (a b : Fin n) (i : Fin 24) : IsSurface (rawLab a b i) := by
  fin_cases i <;> simp [rawLab, posTable, normalTable, IsSurface, coordinate, lo, hi]

private def RubikGeometry.lab (a b : Fin n) (i : Fin 24) : Sticker n := ⟨rawLab a b i, rawLab_isSurface a b i⟩

private def RubikGeometry.genMove (a b : Fin n) : Fin 8 → Move n :=
  ![(0, lo a, 0), (0, hi a, 0), (1, lo a, 0), (1, hi a, 0), (2, lo a, 0), (2, hi a, 0), (0, a, 0),
    (2, b.rev, 0)]

end Labels

private def RubikGeometry.gen0 : Equiv.Perm (Fin 24) where
  toFun := ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 15, 16, 12, 13, 14, 11, 10, 17, 18, 19, 20, 21, 22, 23]
  invFun := ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 16, 15, 12, 13, 14, 10, 11, 17, 18, 19, 20, 21, 22, 23]
  left_inv := by decide
  right_inv := by decide

private def RubikGeometry.gen1 : Equiv.Perm (Fin 24) where
  toFun := ![2, 3, 1, 0, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]
  invFun := ![3, 2, 0, 1, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]
  left_inv := by decide
  right_inv := by decide

private def RubikGeometry.gen2 : Equiv.Perm (Fin 24) where
  toFun := ![0, 1, 2, 3, 4, 5, 6, 7, 8, 17, 10, 11, 12, 13, 14, 15, 16, 18, 19, 9, 20, 21, 22, 23]
  invFun := ![0, 1, 2, 3, 4, 5, 6, 7, 8, 19, 10, 11, 12, 13, 14, 15, 16, 9, 17, 18, 20, 21, 22, 23]
  left_inv := by decide
  right_inv := by decide

private def RubikGeometry.gen3 : Equiv.Perm (Fin 24) where
  toFun := ![0, 1, 2, 3, 12, 5, 6, 7, 8, 9, 10, 11, 13, 14, 4, 15, 16, 17, 18, 19, 20, 21, 22, 23]
  invFun := ![0, 1, 2, 3, 14, 5, 6, 7, 8, 9, 10, 11, 4, 12, 13, 15, 16, 17, 18, 19, 20, 21, 22, 23]
  left_inv := by decide
  right_inv := by decide

private def RubikGeometry.gen4 : Equiv.Perm (Fin 24) where
  toFun := ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 21, 22, 23, 20]
  invFun := ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 23, 20, 21, 22]
  left_inv := by decide
  right_inv := by decide

private def RubikGeometry.gen5 : Equiv.Perm (Fin 24) where
  toFun := ![0, 1, 2, 3, 4, 6, 7, 8, 5, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]
  invFun := ![0, 1, 2, 3, 4, 8, 5, 6, 7, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]
  left_inv := by decide
  right_inv := by decide

private def RubikGeometry.gen6 : Equiv.Perm (Fin 24) where
  toFun := ![0, 1, 2, 3, 5, 19, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 23, 20, 21, 22, 4]
  invFun := ![0, 1, 2, 3, 23, 4, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 5, 20, 21, 22, 19]
  left_inv := by decide
  right_inv := by decide

private def RubikGeometry.gen7 : Equiv.Perm (Fin 24) where
  toFun := ![0, 1, 4, 3, 15, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 17, 16, 2, 18, 19, 20, 21, 22, 23]
  invFun := ![0, 1, 17, 3, 2, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 4, 16, 15, 18, 19, 20, 21, 22, 23]
  left_inv := by decide
  right_inv := by decide

private def RubikGeometry.genPerm : Fin 8 → Equiv.Perm (Fin 24) := ![gen0, gen1, gen2, gen3, gen4, gen5, gen6, gen7]

private def RubikGeometry.commElt {n : ℕ} (a b : Fin n) : Equiv.Perm (Sticker n) :=
  let P := (movePermutation (genMove a b 6))⁻¹ * movePermutation (genMove a b 5) *
      movePermutation (genMove a b 6)
  let Q := movePermutation (genMove a b 7)
  P * Q * P⁻¹ * Q⁻¹

private def RubikGeometry.t0 : Equiv.Perm (Fin 24) :=
  let P := (genPerm 6)⁻¹ * genPerm 5 * genPerm 6
  let Q := genPerm 7
  P * Q * P⁻¹ * Q⁻¹

private def RubikGeometry.orbitGroup {n : ℕ} (a b : Fin n) : Subgroup (Equiv.Perm (Fin 24)) where
  carrier := {τ | ∃ g ∈ moveGroup n, (∀ i, g (lab a b i) = lab a b (τ i)) ∧
      ∀ s, s ∉ Set.range (lab a b) → g s = s}
  one_mem' := ⟨1, Subgroup.one_mem _, by simp, by simp⟩
  mul_mem' := by
    rintro τ₁ τ₂ ⟨g₁, hg₁, h₁, k₁⟩ ⟨g₂, hg₂, h₂, k₂⟩
    refine ⟨g₁ * g₂, Subgroup.mul_mem _ hg₁ hg₂, ?_, ?_⟩
    · intro i; simp [h₁, h₂]
    · intro s hs; simp [k₂ s hs, k₁ s hs]
  inv_mem' := by
    rintro τ ⟨g, hg, h, k⟩
    refine ⟨g⁻¹, Subgroup.inv_mem _ hg, ?_, ?_⟩
    · intro i
      rw [Equiv.Perm.inv_eq_iff_eq, h]; simp
    · intro s hs
      rw [Equiv.Perm.inv_eq_iff_eq, k s hs]

private def RubikGeometry.orbitColourings : ℕ := Nat.factorial 24 / (Nat.factorial 4) ^ 6

open Rubik
@[simp] private theorem RubikGeometry.T.rev_lo {n : ℕ} (a : Fin n) : (lo a).rev = hi a := by
  apply Fin.ext
  simp [lo, hi, Fin.rev]
@[simp] private theorem RubikGeometry.T.rev_hi {n : ℕ} (a : Fin n) : (hi a).rev = lo a := by
  apply Fin.ext
  simp [lo, hi, Fin.rev]
  have := a.isLt
  omega

open Rubik

private def RubikGeometry.T.region {n : ℕ} (s : RawSticker n) : Bool × Bool × Bool × Normal :=
  (decide (2 * s.1.1.val < n), decide (2 * s.1.2.1.val < n),
    decide (2 * s.1.2.2.val < n), s.2)

private def RubikGeometry.T.labelRegion : Fin 24 → Bool × Bool × Bool × Normal :=
  ![
  (false, false, true, (0, true)),
  (false, true, false, (0, true)),
  (false, false, false, (0, true)),
  (false, true, true, (0, true)),
  (true, false, false, (1, true)),
  (true, true, false, (2, true)),
  (false, true, false, (2, true)),
  (false, false, false, (2, true)),
  (true, false, false, (2, true)),
  (true, true, false, (1, false)),
  (true, false, false, (0, false)),
  (true, true, true, (0, false)),
  (false, false, false, (1, true)),
  (false, false, true, (1, true)),
  (true, false, true, (1, true)),
  (true, true, false, (0, false)),
  (true, false, true, (0, false)),
  (false, true, false, (1, false)),
  (false, true, true, (1, false)),
  (true, true, true, (1, false)),
  (true, true, true, (2, false)),
  (false, true, true, (2, false)),
  (false, false, true, (2, false)),
  (true, false, true, (2, false))]

private theorem RubikGeometry.T.labelRegion_injective : Function.Injective labelRegion := by decide

private theorem RubikGeometry.T.region_lab {n : ℕ} {a b : Fin n} (hg : Generic n a b) (i : Fin 24) :
    region (lab a b i).val = labelRegion i := by
  have ha := hg.a_small
  have hb := hg.b_small
  have hal : 2 * a.val < n := by omega
  have hbl : 2 * b.val < n := by omega
  have har : ¬2 * (n - (a.val + 1)) < n := by omega
  have hbr : ¬2 * (n - (b.val + 1)) < n := by omega
  have hlo : 2 * (lo a).val < n := by change 2 * 0 < n; omega
  have hhi : ¬2 * (hi a).val < n := by change ¬2 * (n - 1) < n; omega
  fin_cases i <;> simp [region, labelRegion, lab, rawLab, posTable, normalTable,
    hal, hbl, har, hbr, hlo, hhi]

private def RubikGeometry.T.tangent {n : ℕ} (s : RawSticker n) : Fin n × Fin n :=
  if s.2.1 = 0 then
    if s.2.2 then (s.1.2.1, s.1.2.2) else (s.1.2.1, s.1.2.2.rev)
  else if s.2.1 = 1 then
    if s.2.2 then (s.1.1, s.1.2.2.rev) else (s.1.1, s.1.2.2)
  else if s.2.2 then (s.1.1, s.1.2.1) else (s.1.2.1, s.1.1)

private def RubikGeometry.T.depths {n : ℕ} (s : RawSticker n) : ℕ × ℕ :=
  let (u,v) := tangent s
  if 2 * u.val < n then
    if 2 * v.val < n then (u.val, v.val) else (v.rev.val, u.val)
  else if 2 * v.val < n then (v.val, u.rev.val) else (u.rev.val, v.rev.val)

private theorem RubikGeometry.T.depths_lab {n : ℕ} {a b : Fin n} (hg : Generic n a b) (i : Fin 24) :
    depths (lab a b i).val = (a.val, b.val) := by
  have ha := hg.a_small
  have hb := hg.b_small
  have hal : 2 * a.val < n := by omega
  have hbl : 2 * b.val < n := by omega
  have har : ¬2 * (n - (a.val + 1)) < n := by omega
  have hbr : ¬2 * (n - (b.val + 1)) < n := by omega
  fin_cases i <;> simp [depths, tangent, lab, rawLab, posTable, normalTable,
    hal, hbl, har, hbr]

open Rubik

private theorem RubikGeometry.T.inverse_on_labels {α β : Type*} (f : β → α) (p : Equiv.Perm α) (q : Equiv.Perm β)
    (h : ∀ i, p (f i) = f (q i)) (i : β) : p⁻¹ (f i) = f (q⁻¹ i) := by
  apply p.injective
  simp [h]

private theorem RubikGeometry.T.range_iff {α β : Type*} (f : β → α) (p : Equiv.Perm α) (q : Equiv.Perm β)
    (h : ∀ i, p (f i) = f (q i)) (s : α) :
    p s ∈ Set.range f ↔ s ∈ Set.range f := by
  constructor
  · rintro ⟨i, hi⟩
    refine ⟨q⁻¹ i, p.injective ?_⟩
    rw [h]
    simpa using hi
  · rintro ⟨i, rfl⟩
    exact ⟨q i, (h i).symm⟩

private theorem RubikGeometry.T.commutator_fixed {α : Type*} (O : Set α) (p q : Equiv.Perm α)
    (hp : ∀ s, p s ∈ O ↔ s ∈ O) (hq : ∀ s, q s ∈ O ↔ s ∈ O)
    (hdisj : ∀ s, p s ≠ s → q s ≠ s → s ∈ O) (s : α) (hs : s ∉ O) :
    (p * q * p⁻¹ * q⁻¹) s = s := by
  have hc : ∀ x, x ∉ O → p (q x) = q (p x) := by
    intro x hx
    by_cases hpx : p x = x
    · by_cases hqx : q x = x
      · simp [hpx, hqx]
      · have hqout : q x ∉ O := fun h => hx ((hq x).mp h)
        have hqq : q (q x) ≠ q x := fun h => hqx (q.injective h)
        have hpq : p (q x) = q x := by
          by_contra h
          exact hqout (hdisj (q x) h hqq)
        simp [hpx, hpq]
    · have hqx : q x = x := by
        by_contra h
        exact hx (hdisj x hpx h)
      have hpout : p x ∉ O := fun h => hx ((hp x).mp h)
      have hpp : p (p x) ≠ p x := fun h => hpx (p.injective h)
      have hqp : q (p x) = p x := by
        by_contra h
        exact hpout (hdisj (p x) hpp h)
      simp [hqx, hqp]
  have hqout : q⁻¹ s ∉ O := by
    intro h
    apply hs
    have := (hq (q⁻¹ s)).mpr h
    simpa using this
  have hpout : p⁻¹ (q⁻¹ s) ∉ O := by
    intro h
    apply hqout
    have := (hp (p⁻¹ (q⁻¹ s))).mpr h
    simpa using this
  change p (q (p⁻¹ (q⁻¹ s))) = s
  rw [hc _ hpout]
  simp

private theorem RubikGeometry.T.quarter_support {n : ℕ} (ax : Axis) (l : Fin n) (s : Sticker n)
    (h : movePermutation (ax, l, 0) s ≠ s) : coordinate s.val.1 ax = l := by
  by_contra he
  apply h
  simp [movePermutation, sliceQuarter, he]

private theorem RubikGeometry.T.intersection_sticker {n : ℕ} {a b : Fin n} (hg : Generic n a b) (s : Sticker n)
    (hx : s.val.1.1 = a) (hy : s.val.1.2.1 = hi a) (hz : s.val.1.2.2 = b.rev) :
    s = lab a b 4 := by
  have ha := hg.one_le_a
  have hb := hg.one_le_b
  have has := hg.a_small
  have hbs := hg.b_small
  rcases s with ⟨⟨⟨x,y,z⟩,v,c⟩,hs⟩
  dsimp only at hx hy hz
  subst x; subst y; subst z
  apply Subtype.ext
  fin_cases v <;> cases c <;>
    simp [IsSurface, coordinate, hi, Fin.rev] at hs <;>
    simp [lab, rawLab, posTable, normalTable] <;> omega

open Rubik

private theorem RubikGeometry.T.support_intersection {n : ℕ} {a b : Fin n} (hg : Generic n a b) (s : Sticker n)
    (hp : ((movePermutation (genMove a b 6))⁻¹ * movePermutation (genMove a b 5) *
      movePermutation (genMove a b 6)) s ≠ s)
    (hq : movePermutation (genMove a b 7) s ≠ s) : s ∈ Set.range (lab a b) := by
  let X := movePermutation (genMove a b 6)
  let F := movePermutation (genMove a b 5)
  have hz : s.val.1.2.2 = b.rev := by
    have hq' : movePermutation (2, b.rev, 0) s ≠ s := by simpa [genMove] using hq
    simpa [coordinate] using quarter_support 2 b.rev s hq'
  have hF : F (X s) ≠ X s := by
    intro h
    apply hp
    change X⁻¹ (F (X s)) = s
    rw [h]
    simp
  have hface : coordinate (X s).val.1 2 = hi a := by
    apply quarter_support 2 (hi a) (X s)
    simpa [F, genMove] using hF
  have hbr : b.rev ≠ hi a := by
    intro h
    have hv := congrArg Fin.val h
    simp [hi, Fin.rev] at hv
    have := hg.one_le_b
    have := b.isLt
    omega
  have hx : s.val.1.1 = a := by
    by_contra hxa
    have hfix : X s = s := by
      simp [X, genMove, movePermutation, sliceQuarter, coordinate, hxa]
    apply hbr
    simpa [coordinate, hfix, hz] using hface
  have hXraw : (X s).val.1.2.2 = s.val.1.2.1 := by
    simp [X, genMove, movePermutation, sliceQuarter, coordinate, hx,
      surfaceRotation, rawRotation, coordinateRotation]
  have hy : s.val.1.2.1 = hi a := by
    rw [← hXraw]
    simpa [coordinate] using hface
  exact ⟨4, (intersection_sticker hg s hx hy hz).symm⟩

open Rubik

set_option maxHeartbeats 2000000 in
private theorem RubikGeometry.move_lab {n : ℕ} {a b : Fin n} (hg : Generic n a b) (k : Fin 8) (i : Fin 24) :
    movePermutation (genMove a b k) (lab a b i) = lab a b (genPerm k i) := by
  have ha := hg.one_le_a
  have hb := hg.one_le_b
  have has := hg.a_small
  have hbs := hg.b_small
  have han := a.isLt
  have hbn := b.isLt
  have hab : a.val ≠ b.val := by intro h; exact hg.ne (Fin.ext h)
  have d01 : lo a ≠ a := by
    intro he
    have he' := congrArg Fin.val he
    try simp only [lo, hi, Fin.rev, Fin.val_mk] at he'
    omega
  have d02 : lo a ≠ b := by
    intro he
    have he' := congrArg Fin.val he
    try simp only [lo, hi, Fin.rev, Fin.val_mk] at he'
    omega
  have d03 : lo a ≠ a.rev := by
    intro he
    have he' := congrArg Fin.val he
    try simp only [lo, hi, Fin.rev, Fin.val_mk] at he'
    omega
  have d04 : lo a ≠ b.rev := by
    intro he
    have he' := congrArg Fin.val he
    try simp only [lo, hi, Fin.rev, Fin.val_mk] at he'
    omega
  have d05 : lo a ≠ hi a := by
    intro he
    have he' := congrArg Fin.val he
    try simp only [lo, hi, Fin.rev, Fin.val_mk] at he'
    omega
  have d12 : a ≠ b := by
    intro he
    have he' := congrArg Fin.val he
    try simp only [lo, hi, Fin.rev, Fin.val_mk] at he'
    omega
  have d13 : a ≠ a.rev := by
    intro he
    have he' := congrArg Fin.val he
    try simp only [lo, hi, Fin.rev, Fin.val_mk] at he'
    omega
  have d14 : a ≠ b.rev := by
    intro he
    have he' := congrArg Fin.val he
    try simp only [lo, hi, Fin.rev, Fin.val_mk] at he'
    omega
  have d15 : a ≠ hi a := by
    intro he
    have he' := congrArg Fin.val he
    try simp only [lo, hi, Fin.rev, Fin.val_mk] at he'
    omega
  have d23 : b ≠ a.rev := by
    intro he
    have he' := congrArg Fin.val he
    try simp only [lo, hi, Fin.rev, Fin.val_mk] at he'
    omega
  have d24 : b ≠ b.rev := by
    intro he
    have he' := congrArg Fin.val he
    try simp only [lo, hi, Fin.rev, Fin.val_mk] at he'
    omega
  have d25 : b ≠ hi a := by
    intro he
    have he' := congrArg Fin.val he
    try simp only [lo, hi, Fin.rev, Fin.val_mk] at he'
    omega
  have d34 : a.rev ≠ b.rev := by
    intro he
    have he' := congrArg Fin.val he
    try simp only [lo, hi, Fin.rev, Fin.val_mk] at he'
    omega
  have d35 : a.rev ≠ hi a := by
    intro he
    have he' := congrArg Fin.val he
    try simp only [lo, hi, Fin.rev, Fin.val_mk] at he'
    omega
  have d45 : b.rev ≠ hi a := by
    intro he
    have he' := congrArg Fin.val he
    try simp only [lo, hi, Fin.rev, Fin.val_mk] at he'
    omega
  fin_cases k <;> fin_cases i <;> apply Subtype.ext <;>
    simp [movePermutation, genMove, genPerm, gen0, gen1, gen2, gen3, gen4, gen5, gen6, gen7,
      lab, rawLab, posTable, normalTable, sliceQuarter, surfaceRotation, rawRotation,
      coordinateRotation, normalRotation, normalForward, coordinate, d01, Ne.symm d01, d02, Ne.symm d02, d03, Ne.symm d03, d04, Ne.symm d04, d05, Ne.symm d05, d12, Ne.symm d12, d13, Ne.symm d13, d14, Ne.symm d14, d15, Ne.symm d15, d23, Ne.symm d23, d24, Ne.symm d24, d25, Ne.symm d25, d34, Ne.symm d34, d35, Ne.symm d35, d45, Ne.symm d45]

private theorem RubikGeometry.commElt_lab {n : ℕ} {a b : Fin n} (hg : Generic n a b) (i : Fin 24) :
    commElt a b (lab a b i) = lab a b (t0 i) := by
  have hm := move_lab hg
  have hinv : ∀ k i, (movePermutation (genMove a b k))⁻¹ (lab a b i) =
      lab a b ((genPerm k)⁻¹ i) :=
    fun k i => T.inverse_on_labels _ _ _ (hm k) i
  simp only [commElt, t0, mul_inv_rev, inv_inv, Equiv.Perm.mul_apply, hm, hinv]

private theorem RubikGeometry.commElt_off {n : ℕ} {a b : Fin n} (hg : Generic n a b) (s : Sticker n)
    (hs : s ∉ Set.range (lab a b)) : commElt a b s = s := by
  have hm := move_lab hg
  have hinv : ∀ k i, (movePermutation (genMove a b k))⁻¹ (lab a b i) =
      lab a b ((genPerm k)⁻¹ i) :=
    fun k i => T.inverse_on_labels _ _ _ (hm k) i
  let P := (movePermutation (genMove a b 6))⁻¹ * movePermutation (genMove a b 5) *
    movePermutation (genMove a b 6)
  let Q := movePermutation (genMove a b 7)
  let p := (genPerm 6)⁻¹ * genPerm 5 * genPerm 6
  have hP : ∀ i, P (lab a b i) = lab a b (p i) := by
    intro i
    simp only [P, p, Equiv.Perm.mul_apply, hm, hinv]
  have hQ : ∀ i, Q (lab a b i) = lab a b (genPerm 7 i) := hm 7
  change (P * Q * P⁻¹ * Q⁻¹) s = s
  exact T.commutator_fixed (Set.range (lab a b)) P Q
    (T.range_iff _ _ _ hP) (T.range_iff _ _ _ hQ) (T.support_intersection hg) s hs

private theorem RubikGeometry.lab_injective {n : ℕ} {a b : Fin n} (hg : Generic n a b) :
    Function.Injective (lab a b) := by
  intro i j h
  apply T.labelRegion_injective
  simpa only [T.region_lab hg] using congrArg (fun s : Sticker n => T.region s.val) h

private theorem RubikGeometry.lab_eq_lab {n : ℕ} {a b a' b' : Fin n} (hg : Generic n a b) (hg' : Generic n a' b')
    {i j : Fin 24} (h : lab a b i = lab a' b' j) : a = a' ∧ b = b' := by
  have hh := congrArg (fun s : Sticker n => T.depths s.val) h
  simp only [T.depths_lab hg, T.depths_lab hg'] at hh
  exact ⟨Fin.ext (congrArg Prod.fst hh), Fin.ext (congrArg Prod.snd hh)⟩

open Rubik

private theorem RubikGeometry.G.move_card (n : ℕ) : Fintype.card (Rubik.Move n) = 9 * n := by
  simp only [Fintype.card_prod, Fintype.card_fin]
  omega

private theorem RubikGeometry.G.applyWord_append {n : ℕ} (u v : List (Rubik.Move n))
    (c : Rubik.Colouring n) :
    Rubik.applyWord (u ++ v) c = Rubik.applyWord v (Rubik.applyWord u c) := by
  simp [Rubik.applyWord, List.foldl_append]

private theorem RubikGeometry.G.sliceQuarter_order_four (n : ℕ) (a : Rubik.Axis) (l : Fin n) : Rubik.sliceQuarter n a l ^ 4 = 1 := by
  apply Equiv.ext
  intro s
  have hf : ∀ t : Rubik.Sticker n,
      Rubik.coordinate (Rubik.surfaceRotation n a t).val.1 a = Rubik.coordinate t.val.1 a := by
    intro t
    fin_cases a <;>
      simp [Rubik.surfaceRotation, Rubik.rawRotation, Rubik.coordinateRotation, Rubik.coordinate]
  change Rubik.sliceQuarter n a l (Rubik.sliceQuarter n a l
    (Rubik.sliceQuarter n a l (Rubik.sliceQuarter n a l s))) = s
  by_cases h : Rubik.coordinate s.val.1 a = l
  · simp only [Rubik.sliceQuarter, Equiv.coe_fn_mk, h, if_true, hf]
    apply Subtype.ext
    rcases s with ⟨⟨⟨x, y, z⟩, b, c⟩, hs⟩
    fin_cases a <;> fin_cases b <;> cases c <;>
      simp [Rubik.surfaceRotation, Rubik.rawRotation, Rubik.coordinateRotation,
        Rubik.normalRotation, Rubik.normalForward]
  · simp [Rubik.sliceQuarter, h]

private theorem RubikGeometry.G.stmGraph_connected (n : ℕ) : (Rubik.stmGraph n).Connected := by
  classical
  let p (w : List (Rubik.Move n)) : Rubik.Position n :=
    ⟨Rubik.applyWord w (Rubik.solved n), ⟨w, rfl⟩⟩
  have hstep (w : List (Rubik.Move n)) (m : Rubik.Move n) :
      (Rubik.stmGraph n).Reachable (p w) (p (w ++ [m])) := by
    by_cases h : p w = p (w ++ [m])
    · exact h ▸ SimpleGraph.Reachable.refl (p w)
    · apply SimpleGraph.Adj.reachable
      refine ⟨h, Or.inl ⟨m, ?_⟩⟩
      simp [p, Rubik.applyWord, List.foldl_append]
  have hall : ∀ w : List (Rubik.Move n), (Rubik.stmGraph n).Reachable (p []) (p w) := by
    intro w
    induction w using List.reverseRecOn with
    | nil => exact SimpleGraph.Reachable.refl _
    | append_singleton w m ih => exact ih.trans (hstep w m)
  apply (SimpleGraph.connected_iff_exists_forall_reachable (Rubik.stmGraph n)).mpr
  refine ⟨p [], ?_⟩
  intro c
  obtain ⟨w, hw⟩ := c.property
  have hc : p w = c := Subtype.ext hw
  simpa only [hc] using hall w

private theorem RubikGeometry.G.genericWordCount {State Move : Type*} [Fintype State] [Fintype Move]
    (step : State → Move → State) (start : State) (d : ℕ)
    (cover : ∀ s : State, ∃ w : List Move,
      w.length ≤ d ∧ w.foldl step start = s) :
    Fintype.card State ≤
      ∑ j ∈ Finset.range (d + 1), Fintype.card Move ^ j := by
  classical
  let Words := Σ j : Fin (d + 1), (Fin j.val → Move)
  let eval : Words → State := fun w => (List.ofFn w.2).foldl step start
  have heval : Function.Surjective eval := by
    intro s
    obtain ⟨w, hw, hs⟩ := cover s
    refine ⟨⟨⟨w.length, Nat.lt_succ_of_le hw⟩, w.get⟩, ?_⟩
    simpa [eval] using hs
  calc
    Fintype.card State ≤ Fintype.card Words :=
      Fintype.card_le_of_surjective eval heval
    _ = ∑ j : Fin (d + 1), Fintype.card Move ^ (j : ℕ) := by
      simp [Words, Fintype.card_sigma]
    _ = ∑ j ∈ Finset.range (d + 1), Fintype.card Move ^ j :=
      Fin.sum_univ_eq_sum_range _ (d + 1)

private theorem RubikGeometry.G.move_has_inverse {n : ℕ} (m : Rubik.Move n) :
    ∃ m' : Rubik.Move n, ∀ c : Rubik.Colouring n,
      Rubik.applyMove m' (Rubik.applyMove m c) = c := by
  let m' : Rubik.Move n := (m.1, m.2.1, m.2.2.rev)
  have hsum : (m.2.2.rev.val + 1) + (m.2.2.val + 1) = 4 := by
    simp only [Fin.val_rev]
    have ht := m.2.2.isLt
    omega
  have hprod : Rubik.movePermutation m' * Rubik.movePermutation m = 1 := by
    change (Rubik.sliceQuarter n m.1 m.2.1) ^ (m.2.2.rev.val + 1) *
      (Rubik.sliceQuarter n m.1 m.2.1) ^ (m.2.2.val + 1) = 1
    rw [← pow_add, hsum, sliceQuarter_order_four]
  have hinv : Rubik.movePermutation m' = (Rubik.movePermutation m)⁻¹ :=
    mul_eq_one_iff_eq_inv.mp hprod
  refine ⟨m', ?_⟩
  intro c
  funext s
  change c ((Rubik.movePermutation m).symm ((Rubik.movePermutation m').symm s)) = c s
  rw [hinv]
  exact congrArg c ((Rubik.movePermutation m).symm_apply_apply s)

private theorem RubikGeometry.G.stmGraph_walk_word {n : ℕ} {u v : Rubik.Position n}
    (p : (Rubik.stmGraph n).Walk u v) :
    ∃ w : List (Rubik.Move n),
      w.length = p.length ∧ Rubik.applyWord w u.val = v.val := by
  induction p with
  | nil => exact ⟨[], rfl, rfl⟩
  | @cons u v z h p ih =>
      obtain ⟨w, hwlen, hw⟩ := ih
      have hedge : ∃ m : Rubik.Move n, Rubik.applyMove m u.val = v.val := by
        rcases h.2 with hf | hr
        · exact hf
        · obtain ⟨m, hm⟩ := hr
          obtain ⟨m', hinv⟩ := move_has_inverse m
          refine ⟨m', ?_⟩
          rw [← hm, hinv]
      obtain ⟨m, hm⟩ := hedge
      refine ⟨m :: w, ?_, ?_⟩
      · simp [hwlen]
      · change Rubik.applyWord w (Rubik.applyMove m u.val) = z.val
        rw [hm, hw]

private theorem RubikGeometry.G.diameter_word_cover (n : ℕ) (s : Rubik.Position n) :
    ∃ w : List (Rubik.Move n),
      w.length ≤ Rubik.diameter n ∧ Rubik.applyWord w (Rubik.solved n) = s.val := by
  let start : Rubik.Position n := ⟨Rubik.solved n, ⟨[], rfl⟩⟩
  letI : Nonempty (Rubik.Position n) := ⟨start⟩
  have hc := stmGraph_connected n
  have hfinite : (Rubik.stmGraph n).ediam ≠ ⊤ :=
    (Rubik.stmGraph n).connected_iff_ediam_ne_top.mp hc
  obtain ⟨p, hp⟩ := hc.exists_walk_length_eq_dist start s
  obtain ⟨w, hwlen, hw⟩ := stmGraph_walk_word p
  refine ⟨w, ?_, hw⟩
  calc
    w.length = p.length := hwlen
    _ = (Rubik.stmGraph n).dist start s := hp
    _ ≤ Rubik.diameter n := (Rubik.stmGraph n).dist_le_diam hfinite

private theorem RubikGeometry.G.card_position_le_sum (n : ℕ) :
    Fintype.card (Rubik.Position n) ≤
      ∑ j ∈ Finset.range (Rubik.diameter n + 1), (9 * n) ^ j := by
  classical
  let step : Rubik.Position n → Rubik.Move n → Rubik.Position n := fun s m =>
    ⟨Rubik.applyMove m s.val, by
      obtain ⟨u, hu⟩ := s.property
      refine ⟨u ++ [m], ?_⟩
      rw [applyWord_append, hu]
      rfl⟩
  let start : Rubik.Position n := ⟨Rubik.solved n, ⟨[], rfl⟩⟩
  have hval : ∀ (w : List (Rubik.Move n)) (s : Rubik.Position n),
      (w.foldl step s).val = Rubik.applyWord w s.val := by
    intro w
    induction w with
    | nil => intro s; rfl
    | cons m w ih =>
        intro s
        change (w.foldl step (step s m)).val =
          Rubik.applyWord w (Rubik.applyMove m s.val)
        exact ih (step s m)
  have cover : ∀ s : Rubik.Position n, ∃ w : List (Rubik.Move n),
      w.length ≤ Rubik.diameter n ∧ w.foldl step start = s := by
    intro s
    obtain ⟨w, hwlen, hw⟩ := diameter_word_cover n s
    refine ⟨w, hwlen, ?_⟩
    apply Subtype.ext
    exact (hval w start).trans hw
  simpa only [move_card] using
    (genericWordCount step start (Rubik.diameter n) cover)

private def RubikGeometry.G.act {n : ℕ} (g : Equiv.Perm (Sticker n)) (c : Colouring n) : Colouring n :=
  fun s => c (g.symm s)

private theorem RubikGeometry.G.act_mul {n : ℕ} (g h : Equiv.Perm (Sticker n)) (c : Colouring n) :
    act (g * h) c = act g (act h c) := rfl

private theorem RubikGeometry.G.reachable_applyMove {n : ℕ} {c : Colouring n} (hc : Reachable c)
    (m : Move n) : Reachable (applyMove m c) := by
  obtain ⟨w, hw⟩ := hc
  refine ⟨w ++ [m], ?_⟩
  rw [applyWord_append, hw]
  rfl

private theorem RubikGeometry.G.sum_powers_le (a d : ℕ) :
    (∑ j ∈ Finset.range (d + 1), a ^ j) ≤ (a + 1) ^ d := by
  induction d with
  | zero => simp
  | succ d ih =>
      rw [Finset.sum_range_succ]
      calc
        (∑ j ∈ Finset.range (d + 1), a ^ j) + a ^ (d + 1) ≤
            (a + 1) ^ d + a * (a + 1) ^ d := by
          exact Nat.add_le_add ih (by
            rw [pow_succ']
            exact Nat.mul_le_mul_left a (Nat.pow_le_pow_left (by omega) d))
        _ = (a + 1) ^ (d + 1) := by rw [pow_succ]; ring

open Rubik

private theorem RubikGeometry.reachable_of_moveGroup {n : ℕ} {c : Colouring n} (hc : Reachable c)
    {g : Equiv.Perm (Sticker n)} (hg : g ∈ moveGroup n) :
    Reachable (fun s => c (g.symm s)) := by
  have hp : ∀ g ∈ moveGroup n,
      ∀ c : Colouring n, Reachable (G.act g c) ↔ Reachable c := by
    intro g hg
    induction hg using Subgroup.closure_induction with
    | mem g hg =>
        obtain ⟨m, rfl⟩ := hg
        intro c
        constructor
        · intro h
          obtain ⟨m', hinv⟩ := G.move_has_inverse m
          have h' := G.reachable_applyMove h m'
          change Reachable (applyMove m' (applyMove m c)) at h'
          simpa only [hinv] using h'
        · exact fun hc => G.reachable_applyMove hc m
    | one => intro c; change Reachable c ↔ Reachable c; rfl
    | mul g h hg hh ihg ihh =>
        intro c
        rw [G.act_mul, ihg, ihh]
    | inv g hg ih =>
        intro c
        have h := ih (G.act g⁻¹ c)
        rw [← G.act_mul, mul_inv_cancel] at h
        exact h.symm
  exact (hp g hg c).mpr hc

private theorem RubikGeometry.card_position_le_pow (n : ℕ) :
    Fintype.card (Position n) ≤ (9 * n + 1) ^ diameter n := by
  exact (G.card_position_le_sum n).trans (G.sum_powers_le (9 * n) (diameter n))

open Rubik

private theorem RubikGeometry.F.generators_top : Subgroup.closure (Set.range genPerm) = ⊤ := by
  let H := Subgroup.closure (Set.range genPerm)
  have h (k : Fin 8) : genPerm k ∈ H := Subgroup.subset_closure ⟨k, rfl⟩
  have hr : genPerm 7 * (genPerm 0)⁻¹ * (genPerm 1)⁻¹ * genPerm 3 *
      (genPerm 7)⁻¹ * (genPerm 0)⁻¹ * genPerm 2 * (genPerm 1)⁻¹ *
      genPerm 4 * genPerm 6 * genPerm 5 = finRotate 24 := by decide
  have hrH : finRotate 24 ∈ H := by
    rw [← hr]
    exact H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem
      (H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem (h 7) (H.inv_mem (h 0)))
        (H.inv_mem (h 1))) (h 3)) (H.inv_mem (h 7))) (H.inv_mem (h 0)))
          (h 2)) (H.inv_mem (h 1))) (h 4)) (h 6)) (h 5)
  have hs : (genPerm 3 * genPerm 2 * genPerm 7 * genPerm 1 * genPerm 0 *
      genPerm 1 * genPerm 2 * genPerm 2 * genPerm 6) ^ 63 =
        Equiv.swap (0 : Fin 24) 1 := by
    set_option maxRecDepth 20000 in decide
  have hsH : Equiv.swap (0 : Fin 24) 1 ∈ H := by
    rw [← hs]
    exact H.pow_mem (H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem
      (H.mul_mem (H.mul_mem (H.mul_mem (h 3) (h 2)) (h 7)) (h 1)) (h 0))
        (h 1)) (h 2)) (h 2)) (h 6)) 63
  have hc : Subgroup.closure ({finRotate 24, Equiv.swap (0 : Fin 24) 1} :
      Set (Equiv.Perm (Fin 24))) = ⊤ := by
    simpa using Equiv.Perm.closure_cycle_adjacent_swap
      (isCycle_finRotate (n := 22)) (support_finRotate (n := 22)) (0 : Fin 24)
  apply top_unique
  rw [← hc]
  exact (Subgroup.closure_le _).mpr (by
    intro g hg
    rcases hg with rfl | rfl
    · exact hrH
    · exact hsH)

private theorem RubikGeometry.F.three_t0 : Equiv.Perm.IsThreeCycle t0 := by
  apply card_support_eq_three_iff.mp
  decide

private theorem RubikGeometry.F.gen_mem {n : ℕ} (a b : Fin n) (k : Fin 8) :
    movePermutation (genMove a b k) ∈ moveGroup n :=
  Subgroup.subset_closure ⟨genMove a b k, rfl⟩

private theorem RubikGeometry.F.comm_mem {n : ℕ} (a b : Fin n) : commElt a b ∈ moveGroup n := by
  let H := moveGroup n
  have hP : (movePermutation (genMove a b 6))⁻¹ * movePermutation (genMove a b 5) *
      movePermutation (genMove a b 6) ∈ H :=
    H.mul_mem (H.mul_mem (H.inv_mem (gen_mem a b 6)) (gen_mem a b 5)) (gen_mem a b 6)
  exact H.mul_mem (H.mul_mem (H.mul_mem hP (gen_mem a b 7)) (H.inv_mem hP))
    (H.inv_mem (gen_mem a b 7))

private theorem RubikGeometry.F.inv_lab {n : ℕ} {a b : Fin n} (hg : Generic n a b) (k : Fin 8) (i : Fin 24) :
    (movePermutation (genMove a b k))⁻¹ (lab a b i) =
      lab a b ((genPerm k)⁻¹ i) := by
  rw [Equiv.Perm.inv_eq_iff_eq, move_lab hg]
  simp

private theorem RubikGeometry.F.inv_off {n : ℕ} {a b : Fin n} (hg : Generic n a b) (k : Fin 8)
    {s : Sticker n} (hs : s ∉ Set.range (lab a b)) :
    (movePermutation (genMove a b k))⁻¹ s ∉ Set.range (lab a b) := by
  rintro ⟨i, hi⟩
  apply hs
  refine ⟨genPerm k i, ?_⟩
  rw [← move_lab hg, hi]
  simp

private theorem RubikGeometry.alternating_le_of_closed (T : Subgroup (Equiv.Perm (Fin 24))) (h0 : t0 ∈ T)
    (hconj : ∀ k : Fin 8, ∀ τ ∈ T, genPerm k * τ * (genPerm k)⁻¹ ∈ T) :
    alternatingGroup (Fin 24) ≤ T := by
  have hn : Subgroup.closure (Set.range genPerm) ≤ Subgroup.normalizer (T : Set _) := by
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨k, rfl⟩
    exact Subgroup.mem_normalizer_fintype (hconj k)
  rw [F.generators_top] at hn
  rw [← Equiv.Perm.closure_three_cycles_eq_alternating]
  apply (Subgroup.closure_le _).mpr
  intro c hc
  have hj : IsConj t0 c := Equiv.Perm.isConj_iff_cycleType_eq.mpr (F.three_t0.trans hc.symm)
  obtain ⟨g, hg⟩ := isConj_iff.mp hj
  rw [← hg]
  exact (Subgroup.mem_normalizer_iff.mp (hn (Subgroup.mem_top g)) t0).mp h0

private theorem RubikGeometry.alternating_le_orbitGroup {n : ℕ} {a b : Fin n} (hg : Generic n a b) :
    alternatingGroup (Fin 24) ≤ orbitGroup a b := by
  apply alternating_le_of_closed
  · exact ⟨commElt a b, F.comm_mem a b, commElt_lab hg, commElt_off hg⟩
  · intro k τ hτ
    obtain ⟨g, hgG, hgl, hgo⟩ := hτ
    let P := movePermutation (genMove a b k)
    refine ⟨P * g * P⁻¹,
      (moveGroup n).mul_mem ((moveGroup n).mul_mem (F.gen_mem a b k) hgG)
        ((moveGroup n).inv_mem (F.gen_mem a b k)), ?_, ?_⟩
    · intro i
      simp only [Equiv.Perm.mul_apply]
      change P (g (P⁻¹ (lab a b i))) = lab a b (genPerm k (τ ((genPerm k)⁻¹ i)))
      rw [F.inv_lab hg, hgl, move_lab hg]
    · intro s hs
      change P (g (P⁻¹ s)) = s
      rw [hgo _ (F.inv_off hg k hs)]
      exact P.apply_symm_apply s

private theorem RubikGeometry.card_normalTable_orbit :
    Nat.card {f : Fin 24 → Normal // ∃ σ : Equiv.Perm (Fin 24), f = normalTable ∘ σ} =
      orbitColourings := by
  classical
  let G := DomMulAct (Equiv.Perm (Fin 24))
  have heq : {f : Fin 24 → Normal | ∃ σ : Equiv.Perm (Fin 24), f = normalTable ∘ σ} =
      MulAction.orbit G normalTable := by
    ext f
    constructor
    · rintro ⟨σ, rfl⟩
      exact ⟨DomMulAct.mk σ, rfl⟩
    · rintro ⟨σ, hσ⟩
      exact ⟨DomMulAct.mk.symm σ, hσ.symm⟩
  have hfib : ∀ c : Normal, Fintype.card {i : Fin 24 // normalTable i = c} = 4 := by
    decide
  have hstab : Nat.card (MulAction.stabilizer G normalTable) = (Nat.factorial 4) ^ 6 := by
    calc
      _ = Nat.card {g : Equiv.Perm (Fin 24) // normalTable ∘ g = normalTable} :=
        Nat.card_congr (Equiv.subtypeEquiv DomMulAct.mk.symm (fun _ => Iff.rfl))
      _ = ∏ c : Normal, (Fintype.card {i : Fin 24 // normalTable i = c}).factorial := by
        rw [Nat.card_eq_fintype_card, DomMulAct.stabilizer_card]
      _ = (Nat.factorial 4) ^ 6 := by simp [hfib, Rubik.Normal]
  have hG : Nat.card G = Nat.factorial 24 := by
    rw [Nat.card_congr DomMulAct.mk.symm, Nat.card_eq_fintype_card,
      Fintype.card_perm, Fintype.card_fin]
  have hos := Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup G normalTable)
  rw [Nat.card_prod, hstab, hG] at hos
  calc
    _ = Nat.card (MulAction.orbit G normalTable) := Nat.card_congr (Equiv.setCongr heq)
    _ = orbitColourings := by
      unfold orbitColourings
      exact Nat.eq_div_of_mul_eq_right (by positivity) (by simpa [Nat.mul_comm] using hos)

private theorem RubikGeometry.exists_even_rep (σ : Equiv.Perm (Fin 24)) :
    ∃ σ' ∈ alternatingGroup (Fin 24), normalTable ∘ σ' = normalTable ∘ σ := by
  by_cases hσ : σ ∈ alternatingGroup (Fin 24)
  · exact ⟨σ, hσ, rfl⟩
  have hs : Equiv.Perm.sign σ = -1 := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h
    · exact False.elim (hσ (Equiv.Perm.mem_alternatingGroup.mpr h))
    · exact h
  refine ⟨Equiv.swap (0 : Fin 24) 1 * σ, ?_, ?_⟩
  · rw [Equiv.Perm.mem_alternatingGroup, map_mul, Equiv.Perm.sign_swap (by decide), hs]
    decide
  · have ht : normalTable ∘ Equiv.swap (0 : Fin 24) 1 = normalTable := by decide
    change (normalTable ∘ Equiv.swap (0 : Fin 24) 1) ∘ σ = normalTable ∘ σ
    rw [ht]

open Rubik

private abbrev RubikGeometry.K.Q (n : ℕ) := {p : Fin ((n - 2) / 2) × Fin ((n - 2) / 2) // p.1 ≠ p.2}

private abbrev RubikGeometry.K.S := {f : Fin 24 → Normal // ∃ σ : Equiv.Perm (Fin 24), f = normalTable ∘ σ}

private def RubikGeometry.K.depth {n : ℕ} (i : Fin ((n - 2) / 2)) : Fin n :=
  ⟨i.val + 1, by have := i.isLt; omega⟩

private def RubikGeometry.K.label {n : ℕ} (p : Q n) : Fin 24 → Sticker n :=
  lab (depth p.val.1) (depth p.val.2)

private lemma RubikGeometry.K.generic {n : ℕ} (p : Q n) :
    Generic n (depth p.val.1) (depth p.val.2) := by
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

private lemma RubikGeometry.K.index_eq {n : ℕ} {p q : Q n} {i j : Fin 24}
    (h : label p i = label q j) : p = q := by
  obtain ⟨ha, hb⟩ := lab_eq_lab (generic p) (generic q) h
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

private lemma RubikGeometry.K.recolour {n : ℕ} (p : Q n) (f : S) (c : Colouring n)
    (hc : ∀ i, c (label p i) = normalTable i) :
    ∃ g ∈ moveGroup n,
      (∀ i, c (g.symm (label p i)) = f.val i) ∧
      ∀ q : Q n, q ≠ p → ∀ i, g.symm (label q i) = label q i := by
  classical
  obtain ⟨σ, hσ⟩ := f.property
  obtain ⟨σ', hσ', heq⟩ := exists_even_rep σ
  have hmem : σ'⁻¹ ∈ orbitGroup (depth p.val.1) (depth p.val.2) :=
    alternating_le_orbitGroup (generic p) ((alternatingGroup (Fin 24)).inv_mem hσ')
  obtain ⟨g, hg, hact, hoff⟩ := hmem
  have hact' : ∀ i, g (label p i) = label p (σ'⁻¹ i) := hact
  refine ⟨g, hg, ?_, ?_⟩
  · intro i
    have hinv : g.symm (label p i) = label p (σ' i) := by
      apply g.injective
      simp only [Equiv.apply_symm_apply]
      change label p i = g (label p (σ' i))
      rw [hact']
      simp
    rw [hinv, hc]
    exact congrFun (heq.trans hσ.symm) i
  · intro q hqp i
    have hout : label q i ∉ Set.range (lab (depth p.val.1) (depth p.val.2)) := by
      rintro ⟨j, hj⟩
      exact hqp (index_eq hj).symm
    apply g.injective
    simp only [Equiv.apply_symm_apply]
    exact (hoff _ hout).symm

private lemma RubikGeometry.K.partial_reachable {n : ℕ} (κ : Q n → S) (A : Finset (Q n)) :
    ∃ c : Colouring n, Reachable c ∧
      ∀ p i, c (label p i) = if p ∈ A then (κ p).val i else normalTable i := by
  classical
  induction A using Finset.induction_on with
  | empty =>
    refine ⟨solved n, ⟨[], rfl⟩, ?_⟩
    intro p i
    simp only [Finset.notMem_empty, if_false]
    rfl
  | @insert p A hp ih =>
    obtain ⟨c, hc, hvalues⟩ := ih
    have hpvalues : ∀ i, c (label p i) = normalTable i := by
      intro i
      simpa only [hp, if_false] using hvalues p i
    obtain ⟨g, hg, hnew, hfix⟩ := recolour p (κ p) c hpvalues
    refine ⟨fun s => c (g.symm s), reachable_of_moveGroup hc hg, ?_⟩
    intro q i
    change c (g.symm (label q i)) = if q ∈ insert p A then (κ q).val i else normalTable i
    by_cases hqp : q = p
    · subst q
      simpa only [Finset.mem_insert_self, if_true] using hnew i
    · rw [hfix q hqp i, hvalues q i]
      simp only [Finset.mem_insert, hqp, false_or]

private lemma RubikGeometry.K.all_reachable {n : ℕ} (κ : Q n → S) :
    ∃ c : Position n, ∀ p i, c.val (label p i) = (κ p).val i := by
  classical
  obtain ⟨c, hc, hvalues⟩ := partial_reachable κ Finset.univ
  refine ⟨⟨c, hc⟩, ?_⟩
  intro p i
  simpa only [Finset.mem_univ, if_true] using hvalues p i

private lemma RubikGeometry.K.card_Q (n : ℕ) :
    Fintype.card (Q n) = (n - 2) / 2 * ((n - 2) / 2 - 1) := by
  classical
  let k := (n - 2) / 2
  have hdiag : Fintype.card {p : Fin k × Fin k // p.1 = p.2} = k := by
    let e : {p : Fin k × Fin k // p.1 = p.2} ≃ Fin k :=
      { toFun := fun p => p.val.1
        invFun := fun i => ⟨(i, i), rfl⟩
        left_inv := fun p => Subtype.ext (Prod.ext rfl p.property)
        right_inv := fun _ => rfl }
    exact (Fintype.card_congr e).trans (Fintype.card_fin k)
  change Fintype.card {p : Fin k × Fin k // ¬p.1 = p.2} = k * (k - 1)
  rw [Fintype.card_subtype_compl, Fintype.card_prod, Fintype.card_fin, hdiag]
  rw [Nat.mul_sub_left_distrib, Nat.mul_one]

open Rubik

private theorem RubikGeometry.card_position_ge (n : ℕ) :
    orbitColourings ^ ((n - 2) / 2 * ((n - 2) / 2 - 1)) ≤ Fintype.card (Position n) := by
  classical
  let Φ : (K.Q n → K.S) → Position n := fun κ => Classical.choose (K.all_reachable κ)
  have hΦ : ∀ κ p i, (Φ κ).val (K.label p i) = (κ p).val i :=
    fun κ => Classical.choose_spec (K.all_reachable κ)
  have hinj : Function.Injective Φ := by
    intro κ κ' h
    funext p
    apply Subtype.ext
    funext i
    calc
      (κ p).val i = (Φ κ).val (K.label p i) := (hΦ κ p i).symm
      _ = (Φ κ').val (K.label p i) :=
        congrArg (fun c : Position n => c.val (K.label p i)) h
      _ = (κ' p).val i := hΦ κ' p i
  have hcard := Fintype.card_le_of_injective Φ hinj
  have hS : Fintype.card K.S = orbitColourings := by
    rw [← Nat.card_eq_fintype_card]
    exact card_normalTable_orbit
  simpa only [Fintype.card_fun, hS, K.card_Q] using hcard

open Filter Topology

private theorem RubikGeometry.A.counting_lower (q : ℕ) (hq : 1 ≤ q) (d : ℕ → ℕ)
    (hcount : ∀ n : ℕ, q ^ ((n - 2) / 2 * ((n - 2) / 2 - 1)) ≤ (9 * n + 1) ^ d n)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in Filter.atTop,
      (1 / 4 : ℝ) * Real.log (q : ℝ) - ε ≤
        (d n : ℝ) * Real.log (n : ℝ) / (n : ℝ) ^ 2 := by
  let c : ℝ := (1 / 4 : ℝ) * Real.log (q : ℝ)
  let f : ℕ → ℝ := fun n =>
    c * (1 - 3 / (n : ℝ)) * (1 - 5 / (n : ℝ)) *
      (1 + Real.log 10 / Real.log (n : ℝ))⁻¹
  have hnat : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hlogNat : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp hnat
  have hthree : Tendsto (fun n : ℕ => (1 : ℝ) - 3 / (n : ℝ)) atTop (𝓝 1) := by
    simpa using (tendsto_const_nhds.sub
      ((tendsto_const_nhds : Tendsto (fun _ : ℕ => (3 : ℝ)) atTop (𝓝 3)).div_atTop hnat))
  have hfive : Tendsto (fun n : ℕ => (1 : ℝ) - 5 / (n : ℝ)) atTop (𝓝 1) := by
    simpa using (tendsto_const_nhds.sub
      ((tendsto_const_nhds : Tendsto (fun _ : ℕ => (5 : ℝ)) atTop (𝓝 5)).div_atTop hnat))
  have hlogdiv : Tendsto (fun n : ℕ => Real.log 10 / Real.log (n : ℝ))
      atTop (𝓝 0) := tendsto_const_nhds.div_atTop hlogNat
  have hdenlim : Tendsto (fun n : ℕ => 1 + Real.log 10 / Real.log (n : ℝ))
      atTop (𝓝 1) := by
    simpa using (tendsto_const_nhds.add hlogdiv)
  have hlast : Tendsto (fun n : ℕ => (1 + Real.log 10 / Real.log (n : ℝ))⁻¹)
      atTop (𝓝 1) := by
    simpa using hdenlim.inv₀ (by norm_num : (1 : ℝ) ≠ 0)
  have hc : Tendsto (fun _ : ℕ => c) atTop (𝓝 c) := tendsto_const_nhds
  have hf : Tendsto f atTop (𝓝 c) := by
    simpa [f] using ((hc.mul hthree).mul hfive).mul hlast
  have hevent : ∀ᶠ n : ℕ in atTop, c - ε < f n :=
    (tendsto_order.1 hf).1 (c - ε) (by linarith)
  have hqR : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hqpos : (0 : ℝ) < (q : ℝ) := lt_of_lt_of_le zero_lt_one hqR
  have hlogq : 0 ≤ Real.log (q : ℝ) := Real.log_nonneg hqR
  filter_upwards [hevent, eventually_ge_atTop (6 : ℕ)] with n he hn
  refine he.le.trans ?_
  have hnR : (6 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
  have hln : 0 < Real.log (n : ℝ) := Real.log_pos (by linarith)
  have hlten : 0 < Real.log (10 : ℝ) := Real.log_pos (by norm_num)
  have hden : 0 < Real.log (n : ℝ) + Real.log 10 := by positivity
  let k : ℕ := (n - 2) / 2
  have hk : n ≤ 2 * k + 3 := by dsimp [k]; omega
  have hk' : n ≤ 2 * (k - 1) + 5 := by dsimp [k]; omega
  have hkR : (n : ℝ) ≤ 2 * (k : ℝ) + 3 := by exact_mod_cast hk
  have hkR' : (n : ℝ) ≤ 2 * ((k - 1 : ℕ) : ℝ) + 5 := by exact_mod_cast hk'
  have hm : ((n : ℝ) - 3) * ((n : ℝ) - 5) / 4 ≤ ((k * (k - 1) : ℕ) : ℝ) := by
    rw [Nat.cast_mul]
    have hm' := mul_le_mul
      (show (n : ℝ) - 3 ≤ 2 * (k : ℝ) by linarith)
      (show (n : ℝ) - 5 ≤ 2 * ((k - 1 : ℕ) : ℝ) by linarith)
      (by linarith : (0 : ℝ) ≤ (n : ℝ) - 5)
      (by positivity : (0 : ℝ) ≤ 2 * (k : ℝ))
    nlinarith
  have hcountR : (q : ℝ) ^ (k * (k - 1)) ≤ (9 * (n : ℝ) + 1) ^ d n := by
    exact_mod_cast hcount n
  have hlogs : ((k * (k - 1) : ℕ) : ℝ) * Real.log (q : ℝ) ≤
      (d n : ℝ) * Real.log (9 * (n : ℝ) + 1) := by
    simpa only [Real.log_pow] using
      Real.log_le_log (pow_pos hqpos _) hcountR
  have hlogbound : Real.log (9 * (n : ℝ) + 1) ≤
      Real.log (n : ℝ) + Real.log 10 := by
    have hb := Real.log_le_log
      (by positivity : (0 : ℝ) < 9 * (n : ℝ) + 1)
      (show 9 * (n : ℝ) + 1 ≤ 10 * (n : ℝ) by linarith)
    rw [Real.log_mul (by norm_num : (10 : ℝ) ≠ 0) hnpos.ne'] at hb
    simpa [add_comm] using hb
  have hmain : (((n : ℝ) - 3) * ((n : ℝ) - 5) / 4) * Real.log (q : ℝ) ≤
      (d n : ℝ) * (Real.log (n : ℝ) + Real.log 10) :=
    (mul_le_mul_of_nonneg_right hm hlogq).trans
      (hlogs.trans (mul_le_mul_of_nonneg_left hlogbound (Nat.cast_nonneg _)))
  have hd : ((((n : ℝ) - 3) * ((n : ℝ) - 5) / 4) * Real.log (q : ℝ)) /
      (Real.log (n : ℝ) + Real.log 10) ≤ (d n : ℝ) :=
    (div_le_iff₀ hden).2 hmain
  calc
    f n = (((((n : ℝ) - 3) * ((n : ℝ) - 5) / 4) * Real.log (q : ℝ)) /
        (Real.log (n : ℝ) + Real.log 10)) * (Real.log (n : ℝ) / (n : ℝ) ^ 2) := by
      dsimp [f, c]
      field_simp
      <;> ring
    _ ≤ (d n : ℝ) * (Real.log (n : ℝ) / (n : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_right hd (div_nonneg hln.le (sq_nonneg _))
    _ = (d n : ℝ) * Real.log (n : ℝ) / (n : ℝ) ^ 2 := by ring

open Rubik

private theorem RubikGeometry.lower_half (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in Filter.atTop, entropyConstant - ε ≤ normalizedDiameter n := by
  have hq : 1 ≤ orbitColourings := by norm_num [orbitColourings, Nat.factorial]
  have hqcast : (orbitColourings : ℝ) =
      (Nat.factorial 24 : ℝ) / (Nat.factorial 4 : ℝ) ^ 6 := by
    norm_num [orbitColourings, Nat.factorial]
  have hcount : ∀ n : ℕ,
      orbitColourings ^ ((n - 2) / 2 * ((n - 2) / 2 - 1)) ≤ (9 * n + 1) ^ diameter n :=
    fun n => (card_position_ge n).trans (card_position_le_pow n)
  simpa only [entropyConstant, normalizedDiameter, hqcast] using
    A.counting_lower orbitColourings hq diameter hcount ε hε

private theorem rubik_slice_diameter_lower_bound (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in Filter.atTop, Rubik.entropyConstant - ε ≤ Rubik.normalizedDiameter n :=
  RubikGeometry.lower_half ε hε

theorem proof_RubikAsymptotics_lowerTail (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in Filter.atTop, Rubik.entropyConstant - ε ≤ Rubik.normalizedDiameter n :=
  RubikGeometry.lower_half ε hε
