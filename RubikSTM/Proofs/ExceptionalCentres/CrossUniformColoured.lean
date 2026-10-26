import Mathlib
import RubikSTM.Definitions.ExceptionalCentres.CrossThreeCycle
import RubikSTM.Definitions.Orbits.RigidLabelPermutation
import RubikSTM.Definitions.Channel.Colour.OrbitAction
set_option autoImplicit false
open Rubik RubikGeometry RubikExceptional

@[simp] private theorem RubikExceptional.rev_lo {n : ℕ} (a : Fin n) : (lo a).rev = hi a := by
  apply Fin.ext
  simp [lo, hi, Fin.rev]
@[simp] private theorem RubikExceptional.rev_hi {n : ℕ} (a : Fin n) : (hi a).rev = lo a := by
  apply Fin.ext
  simp [lo, hi, Fin.rev]
  have := a.isLt
  omega

open Rubik

private theorem RubikExceptional.inverse_on_labels {α β : Type*} (f : β → α) (p : Equiv.Perm α) (q : Equiv.Perm β)
    (h : ∀ i, p (f i) = f (q i)) (i : β) : p⁻¹ (f i) = f (q⁻¹ i) := by
  apply p.injective
  simp [h]

private theorem RubikExceptional.range_iff {α β : Type*} (f : β → α) (p : Equiv.Perm α) (q : Equiv.Perm β)
    (h : ∀ i, p (f i) = f (q i)) (s : α) :
    p s ∈ Set.range f ↔ s ∈ Set.range f := by
  constructor
  · rintro ⟨i, hi⟩
    refine ⟨q⁻¹ i, p.injective ?_⟩
    rw [h]
    simpa using hi
  · rintro ⟨i, rfl⟩
    exact ⟨q i, (h i).symm⟩

private theorem RubikExceptional.commutator_fixed {α : Type*} (O : Set α) (p q : Equiv.Perm α)
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

private theorem RubikExceptional.quarter_support {n : ℕ} (ax : Axis) (l : Fin n) (s : Sticker n)
    (h : movePermutation (ax, l, 0) s ≠ s) : coordinate s.val.1 ax = l := by
  by_contra he
  apply h
  simp [movePermutation, sliceQuarter, he]

private theorem RubikExceptional.intersection_sticker {n : ℕ} {a b : Fin n} (ha : 1 ≤ a.val) (has : a.val + 1 < n)
    (hb : 1 ≤ b.val) (hbs : b.val + 1 < n) (s : Sticker n)
    (hx : s.val.1.1 = a) (hy : s.val.1.2.1 = hi a) (hz : s.val.1.2.2 = b.rev) :
    s = lab a b 4 := by
  rcases s with ⟨⟨⟨x,y,z⟩,v,c⟩,hs⟩
  dsimp only at hx hy hz
  subst x; subst y; subst z
  apply Subtype.ext
  fin_cases v <;> cases c <;>
    simp [IsSurface, coordinate, hi, Fin.rev] at hs <;>
    simp [lab, rawLab, posTable, normalTable] <;> omega
private theorem RubikExceptional.support_intersection {n : ℕ} {a b : Fin n} (ha : 1 ≤ a.val) (has : a.val + 1 < n)
    (hb : 1 ≤ b.val) (hbs : b.val + 1 < n) (s : Sticker n)
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
    have := hb
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
  exact ⟨4, (intersection_sticker ha has hb hbs s hx hy hz).symm⟩

open Rubik RubikGeometry RubikExceptional
set_option maxHeartbeats 2500000

private theorem RubikExceptional.cross_injective {n : ℕ} {a b : Fin n}
    (ha : Regular n a) (hb : b.rev=b) : Function.Injective (lab a b) := by
  have hap := ha.positive
  have has := ha.small
  have han := a.isLt
  have hbn := b.isLt
  have hc : 2*b.val+1=n := by
    have hv := congrArg Fin.val hb
    simp only [Fin.val_rev] at hv
    omega
  have d01 : lo a ≠ a := by
    intro h
    have hv := congrArg Fin.val h
    try simp [lo,hi,Fin.rev] at hv
    omega
  have d02 : lo a ≠ b := by
    intro h
    have hv := congrArg Fin.val h
    try simp [lo,hi,Fin.rev] at hv
    omega
  have d03 : lo a ≠ a.rev := by
    intro h
    have hv := congrArg Fin.val h
    try simp [lo,hi,Fin.rev] at hv
    omega
  have d04 : lo a ≠ hi a := by
    intro h
    have hv := congrArg Fin.val h
    try simp [lo,hi,Fin.rev] at hv
    omega
  have d12 : a ≠ b := by
    intro h
    have hv := congrArg Fin.val h
    try simp [lo,hi,Fin.rev] at hv
    omega
  have d13 : a ≠ a.rev := by
    intro h
    have hv := congrArg Fin.val h
    try simp [lo,hi,Fin.rev] at hv
    omega
  have d14 : a ≠ hi a := by
    intro h
    have hv := congrArg Fin.val h
    try simp [lo,hi,Fin.rev] at hv
    omega
  have d23 : b ≠ a.rev := by
    intro h
    have hv := congrArg Fin.val h
    try simp [lo,hi,Fin.rev] at hv
    omega
  have d24 : b ≠ hi a := by
    intro h
    have hv := congrArg Fin.val h
    try simp [lo,hi,Fin.rev] at hv
    omega
  have d34 : a.rev ≠ hi a := by
    intro h
    have hv := congrArg Fin.val h
    try simp [lo,hi,Fin.rev] at hv
    omega
  let code (x : Fin n) : ℕ :=
    if x=lo a then 0 else if x=a then 1 else if x=b then 2 else if x=a.rev then 3 else 4
  let region (s : RawSticker n) : ℕ × ℕ × ℕ × Normal :=
    (code s.1.1,code s.1.2.1,code s.1.2.2,s.2)
  let table : Fin 24 → ℕ × ℕ × ℕ × Normal :=
    ![(4,2,1,(0,true)),
    (4,2,3,(0,true)),
    (4,3,2,(0,true)),
    (4,1,2,(0,true)),
    (1,4,2,(1,true)),
    (1,2,4,(2,true)),
    (2,1,4,(2,true)),
    (3,2,4,(2,true)),
    (2,3,4,(2,true)),
    (2,0,3,(1,false)),
    (0,2,3,(0,false)),
    (0,2,1,(0,false)),
    (2,4,3,(1,true)),
    (3,4,2,(1,true)),
    (2,4,1,(1,true)),
    (0,1,2,(0,false)),
    (0,3,2,(0,false)),
    (3,0,2,(1,false)),
    (2,0,1,(1,false)),
    (1,0,2,(1,false)),
    (2,1,0,(2,false)),
    (3,2,0,(2,false)),
    (2,3,0,(2,false)),
    (1,2,0,(2,false))]
  have hinj : Function.Injective table := by decide
  have hreg (i : Fin 24) : region (lab a b i).val = table i := by
    fin_cases i <;> simp [region,code,table,lab,rawLab,posTable,normalTable,hb,d01, Ne.symm d01, d02, Ne.symm d02, d03, Ne.symm d03, d04, Ne.symm d04, d12, Ne.symm d12, d13, Ne.symm d13, d14, Ne.symm d14, d23, Ne.symm d23, d24, Ne.symm d24, d34, Ne.symm d34]
  intro i j h
  apply hinj
  simpa only [hreg] using congrArg (fun s : Sticker n => region s.val) h

private theorem RubikExceptional.cross_move_lab {n : ℕ} {a b : Fin n}
    (ha : Regular n a) (hb : b.rev=b) (k : Fin 8) (i : Fin 24) :
    movePermutation (genMove a b k) (lab a b i) = lab a b (crossGen k i) := by
  have hap := ha.positive
  have has := ha.small
  have han := a.isLt
  have hbn := b.isLt
  have hc : 2*b.val+1=n := by
    have hv := congrArg Fin.val hb
    simp only [Fin.val_rev] at hv
    omega
  have d01 : lo a ≠ a := by
    intro h
    have hv := congrArg Fin.val h
    try simp [lo,hi,Fin.rev] at hv
    omega
  have d02 : lo a ≠ b := by
    intro h
    have hv := congrArg Fin.val h
    try simp [lo,hi,Fin.rev] at hv
    omega
  have d03 : lo a ≠ a.rev := by
    intro h
    have hv := congrArg Fin.val h
    try simp [lo,hi,Fin.rev] at hv
    omega
  have d04 : lo a ≠ hi a := by
    intro h
    have hv := congrArg Fin.val h
    try simp [lo,hi,Fin.rev] at hv
    omega
  have d12 : a ≠ b := by
    intro h
    have hv := congrArg Fin.val h
    try simp [lo,hi,Fin.rev] at hv
    omega
  have d13 : a ≠ a.rev := by
    intro h
    have hv := congrArg Fin.val h
    try simp [lo,hi,Fin.rev] at hv
    omega
  have d14 : a ≠ hi a := by
    intro h
    have hv := congrArg Fin.val h
    try simp [lo,hi,Fin.rev] at hv
    omega
  have d23 : b ≠ a.rev := by
    intro h
    have hv := congrArg Fin.val h
    try simp [lo,hi,Fin.rev] at hv
    omega
  have d24 : b ≠ hi a := by
    intro h
    have hv := congrArg Fin.val h
    try simp [lo,hi,Fin.rev] at hv
    omega
  have d34 : a.rev ≠ hi a := by
    intro h
    have hv := congrArg Fin.val h
    try simp [lo,hi,Fin.rev] at hv
    omega
  fin_cases k <;> fin_cases i <;> apply Subtype.ext <;>
    simp [movePermutation,genMove,crossGen,crossGen0,crossGen1,crossGen2,crossGen3,crossGen4,crossGen5,crossGen6,crossGen7,
      lab,rawLab,posTable,normalTable,sliceQuarter,surfaceRotation,rawRotation,
      coordinateRotation,normalRotation,normalForward,coordinate,hb,d01, Ne.symm d01, d02, Ne.symm d02, d03, Ne.symm d03, d04, Ne.symm d04, d12, Ne.symm d12, d13, Ne.symm d13, d14, Ne.symm d14, d23, Ne.symm d23, d24, Ne.symm d24, d34, Ne.symm d34]

private theorem RubikExceptional.cross_control_lab {n : ℕ} {a b : Fin n}
    (ha : Regular n a) (hb : b.rev=b) (k : Fin 9) (i : Fin 24) :
    movePermutation (crossControlMove a k) (lab a b i) = lab a b (crossControl k i) := by
  have hap := ha.positive
  have has := ha.small
  have han := a.isLt
  have hbn := b.isLt
  have hc : 2*b.val+1=n := by
    have hv := congrArg Fin.val hb
    simp only [Fin.val_rev] at hv
    omega
  have d01 : lo a ≠ a := by
    intro h
    have hv := congrArg Fin.val h
    try simp [lo,hi,Fin.rev] at hv
    omega
  have d02 : lo a ≠ b := by
    intro h
    have hv := congrArg Fin.val h
    try simp [lo,hi,Fin.rev] at hv
    omega
  have d03 : lo a ≠ a.rev := by
    intro h
    have hv := congrArg Fin.val h
    try simp [lo,hi,Fin.rev] at hv
    omega
  have d04 : lo a ≠ hi a := by
    intro h
    have hv := congrArg Fin.val h
    try simp [lo,hi,Fin.rev] at hv
    omega
  have d12 : a ≠ b := by
    intro h
    have hv := congrArg Fin.val h
    try simp [lo,hi,Fin.rev] at hv
    omega
  have d13 : a ≠ a.rev := by
    intro h
    have hv := congrArg Fin.val h
    try simp [lo,hi,Fin.rev] at hv
    omega
  have d14 : a ≠ hi a := by
    intro h
    have hv := congrArg Fin.val h
    try simp [lo,hi,Fin.rev] at hv
    omega
  have d23 : b ≠ a.rev := by
    intro h
    have hv := congrArg Fin.val h
    try simp [lo,hi,Fin.rev] at hv
    omega
  have d24 : b ≠ hi a := by
    intro h
    have hv := congrArg Fin.val h
    try simp [lo,hi,Fin.rev] at hv
    omega
  have d34 : a.rev ≠ hi a := by
    intro h
    have hv := congrArg Fin.val h
    try simp [lo,hi,Fin.rev] at hv
    omega
  fin_cases k
  · exact cross_move_lab ha hb 0 i
  · exact cross_move_lab ha hb 1 i
  · exact cross_move_lab ha hb 2 i
  · exact cross_move_lab ha hb 3 i
  · exact cross_move_lab ha hb 4 i
  · exact cross_move_lab ha hb 5 i
  · exact cross_move_lab ha hb 6 i
  · fin_cases i <;> apply Subtype.ext <;>
      simp [movePermutation,crossControlMove,crossControl,crossControlGen0,crossControlGen1,crossControlGen2,crossControlGen3,crossControlGen4,crossControlGen5,crossControlGen6,crossControlGen7,crossControlGen8,
        lab,rawLab,posTable,normalTable,sliceQuarter,surfaceRotation,rawRotation,
        coordinateRotation,normalRotation,normalForward,coordinate,hb,d01, Ne.symm d01, d02, Ne.symm d02, d03, Ne.symm d03, d04, Ne.symm d04, d12, Ne.symm d12, d13, Ne.symm d13, d14, Ne.symm d14, d23, Ne.symm d23, d24, Ne.symm d24, d34, Ne.symm d34]
  · fin_cases i <;> apply Subtype.ext <;>
      simp [movePermutation,crossControlMove,crossControl,crossControlGen0,crossControlGen1,crossControlGen2,crossControlGen3,crossControlGen4,crossControlGen5,crossControlGen6,crossControlGen7,crossControlGen8,
        lab,rawLab,posTable,normalTable,sliceQuarter,surfaceRotation,rawRotation,
        coordinateRotation,normalRotation,normalForward,coordinate,hb,d01, Ne.symm d01, d02, Ne.symm d02, d03, Ne.symm d03, d04, Ne.symm d04, d12, Ne.symm d12, d13, Ne.symm d13, d14, Ne.symm d14, d23, Ne.symm d23, d24, Ne.symm d24, d34, Ne.symm d34]
private theorem RubikExceptional.cross_comm_lab {n : ℕ} {a b : Fin n} (ha : Regular n a) (hb : b.rev=b) (i : Fin 24) :
    commElt a b (lab a b i) = lab a b (crossThreeCycle i) := by
  have hm := cross_move_lab ha hb
  have hinv : ∀ k i, (movePermutation (genMove a b k))⁻¹ (lab a b i) =
      lab a b ((crossGen k)⁻¹ i) :=
    fun k i => inverse_on_labels _ _ _ (hm k) i
  simp only [commElt, crossThreeCycle, mul_inv_rev, inv_inv, Equiv.Perm.mul_apply, hm, hinv]

private theorem RubikExceptional.cross_comm_off {n : ℕ} {a b : Fin n} (ha : Regular n a) (hb : b.rev=b) (s : Sticker n)
    (hs : s ∉ Set.range (lab a b)) : commElt a b s = s := by
  have hm := cross_move_lab ha hb
  have hinv : ∀ k i, (movePermutation (genMove a b k))⁻¹ (lab a b i) =
      lab a b ((crossGen k)⁻¹ i) :=
    fun k i => inverse_on_labels _ _ _ (hm k) i
  let P := (movePermutation (genMove a b 6))⁻¹ * movePermutation (genMove a b 5) *
    movePermutation (genMove a b 6)
  let Q := movePermutation (genMove a b 7)
  let p := (crossGen 6)⁻¹ * crossGen 5 * crossGen 6
  have hP : ∀ i, P (lab a b i) = lab a b (p i) := by
    intro i
    simp only [P,p,Equiv.Perm.mul_apply,hm,hinv]
  have hQ : ∀ i, Q (lab a b i) = lab a b (crossGen 7 i) := hm 7
  change (P * Q * P⁻¹ * Q⁻¹) s = s
  exact commutator_fixed (Set.range (lab a b)) P Q
    (range_iff _ _ _ hP) (range_iff _ _ _ hQ)
    (support_intersection ha.positive (by have := ha.small; omega)
      (by
        have hv := congrArg Fin.val hb
        have := ha.small; have := ha.positive
        simp only [Fin.val_rev] at hv
        have := b.isLt
        omega) (by
        have hv := congrArg Fin.val hb
        have := ha.small; have := ha.positive
        simp only [Fin.val_rev] at hv
        have := b.isLt
        omega)) s hs

private theorem RubikExceptional.cross_primitive {n : ℕ} (a b : Fin n) (ha : Regular n a) (hb : b.rev=b) :
    Function.Injective (lab a b) ∧ crossThreeCycle.IsThreeCycle ∧
    (∀ i, commElt a b (lab a b i) = lab a b (crossThreeCycle i)) ∧
    ∀ s, s ∉ Set.range (lab a b) → commElt a b s = s := by
  refine ⟨cross_injective ha hb,?_,cross_comm_lab ha hb,cross_comm_off ha hb⟩
  apply card_support_eq_three_iff.mp
  decide
open RubikExceptional Equiv.Perm
set_option maxRecDepth 30000
set_option maxHeartbeats 700000

private theorem RubikExceptional.cross_control_top : Subgroup.closure (Set.range crossControl) = ⊤ := by
  let H := Subgroup.closure (Set.range crossControl)
  have h (k : Fin 9) : crossControl k ∈ H := Subgroup.subset_closure ⟨k,rfl⟩
  let r : Equiv.Perm (Fin 24) := (crossControl 6)⁻¹ * (crossControl 8)⁻¹ * (crossControl 8) * (crossControl 3)⁻¹ * (crossControl 4)⁻¹ * (crossControl 2) * (crossControl 1)⁻¹ * (crossControl 6)⁻¹ * (crossControl 7) * (crossControl 2)⁻¹ * (crossControl 2) * (crossControl 5)⁻¹ * (crossControl 7) * (crossControl 0)⁻¹ * (crossControl 6)⁻¹
  let s : Equiv.Perm (Fin 24) := ((crossControl 1) * (crossControl 4) * (crossControl 0) * (crossControl 0) * (crossControl 5)⁻¹ * (crossControl 0)⁻¹ * (crossControl 4) * (crossControl 2) * (crossControl 1) * (crossControl 1)⁻¹ * (crossControl 1)⁻¹ * (crossControl 7)⁻¹ * (crossControl 8)) ^ 17
  have hrH : r ∈ H := (H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem (H.inv_mem (h 6)) (H.inv_mem (h 8))) (h 8)) (H.inv_mem (h 3))) (H.inv_mem (h 4))) (h 2)) (H.inv_mem (h 1))) (H.inv_mem (h 6))) (h 7)) (H.inv_mem (h 2))) (h 2)) (H.inv_mem (h 5))) (h 7)) (H.inv_mem (h 0))) (H.inv_mem (h 6)))
  have hsH : s ∈ H := H.pow_mem (H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem (h 1) (h 4)) (h 0)) (h 0)) (H.inv_mem (h 5))) (H.inv_mem (h 0))) (h 4)) (h 2)) (h 1)) (H.inv_mem (h 1))) (H.inv_mem (h 1))) (H.inv_mem (h 7))) (h 8)) 17
  let e : Equiv.Perm (Fin 24) :=
    { toFun := ![0, 3, 15, 10, 16, 11, 14, 13, 12, 23, 4, 9, 17, 18, 5, 22, 21, 20, 6, 19, 8, 7, 1, 2]
      invFun := ![0, 22, 23, 1, 10, 14, 18, 21, 20, 11, 3, 5, 8, 7, 6, 2, 4, 12, 13, 19, 17, 16, 15, 9]
      left_inv := by decide
      right_inv := by decide }
  have hr : r = e * finRotate 24 * e⁻¹ := by decide
  have hcycle : r.IsCycle := by
    rw [hr]
    exact (isCycle_finRotate (n := 22)).conj
  have hsupp : r.support = Finset.univ := by decide
  have hswap : s = Equiv.swap (21 : Fin 24) ((r ^ 17) 21) := by decide
  have htop : Subgroup.closure ({r, Equiv.swap (21 : Fin 24) ((r ^ 17) 21)} :
      Set (Equiv.Perm (Fin 24))) = ⊤ :=
    closure_cycle_coprime_swap (by decide : Nat.Coprime 17 (Fintype.card (Fin 24)))
      hcycle hsupp 21
  apply top_unique
  rw [← htop]
  apply (Subgroup.closure_le _).mpr
  intro g hg
  rcases hg with rfl | rfl
  · exact hrH
  · rw [← hswap]
    exact hsH
open Rubik RubikGeometry RubikExceptional

private theorem RubikExceptional.quarter_order_four (n : ℕ) (a : Rubik.Axis) (l : Fin n) : Rubik.sliceQuarter n a l ^ 4 = 1 := by
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

private theorem RubikExceptional.inverse_move_perm {n : ℕ} (m : Move n) :
    movePermutation (inverseMove m) = (movePermutation m)⁻¹ := by
  apply mul_eq_one_iff_eq_inv.mp
  change (sliceQuarter n m.1 m.2.1) ^ (m.2.2.rev.val + 1) *
    (sliceQuarter n m.1 m.2.1) ^ (m.2.2.val + 1) = 1
  rw [← pow_add, show (m.2.2.rev.val+1)+(m.2.2.val+1)=4 by
    simp only [Fin.val_rev]; have := m.2.2.isLt; omega, quarter_order_four]

@[simp] private theorem RubikExceptional.word_nil {n : ℕ} : wordPerm ([] : List (Move n)) = 1 := rfl

@[simp] private theorem RubikExceptional.word_singleton {n : ℕ} (m : Move n) :
    wordPerm [m] = movePermutation m := by simp [wordPerm]

private theorem RubikExceptional.word_append {n : ℕ} (u v : List (Move n)) :
    wordPerm (u ++ v) = wordPerm v * wordPerm u := by
  simp [wordPerm,List.reverse_append,List.prod_append]

private theorem RubikExceptional.word_cons {n : ℕ} (m : Move n) (w : List (Move n)) :
    wordPerm (m :: w) = wordPerm w * movePermutation m := by
  simpa using word_append [m] w

@[simp] private theorem RubikExceptional.inverse_word_length {n : ℕ} (w : List (Move n)) :
    (inverseWord w).length = w.length := by simp [inverseWord]

private theorem RubikExceptional.word_inverse {n : ℕ} (w : List (Move n)) :
    wordPerm (inverseWord w) = (wordPerm w)⁻¹ := by
  induction w with
  | nil => simp [inverseWord]
  | cons m w ih =>
    have hs : inverseWord (m::w) = inverseWord w ++ [inverseMove m] := by
      simp [inverseWord]
    rw [hs,word_append,word_singleton,inverse_move_perm,ih,word_cons,mul_inv_rev]

private theorem RubikExceptional.applyWord_wordPerm {n : ℕ} (w : List (Move n)) (c : Colouring n) :
    applyWord w c = fun s => c ((wordPerm w)⁻¹ s) := by
  induction w generalizing c with
  | nil => rfl
  | cons m w ih =>
    rw [show applyWord (m::w) c = applyWord w (applyMove m c) by rfl, ih,word_cons,mul_inv_rev]
    rfl

private theorem RubikExceptional.solves_inverse {n : ℕ} {a : Fin n} {τ : Equiv.Perm (Fin 24)}
    {w : List (Move n)} (hw : DiagonalSolves a τ w) :
    DiagonalSolves a τ⁻¹ (inverseWord w) := by
  constructor
  · intro i
    rw [word_inverse]
    apply (wordPerm w).injective
    simp [hw.1]
  · intro s hs
    rw [word_inverse]
    apply (wordPerm w).injective
    simp [hw.2 s hs]

private theorem RubikExceptional.solves_mul {n : ℕ} {a : Fin n} {σ τ : Equiv.Perm (Fin 24)}
    {u v : List (Move n)} (hu : DiagonalSolves a σ u) (hv : DiagonalSolves a τ v) :
    DiagonalSolves a (σ * τ) (v ++ u) := by
  constructor
  · intro i
    simp only [word_append,Equiv.Perm.mul_apply,hu.1,hv.1]
  · intro s hs
    simp only [word_append,Equiv.Perm.mul_apply,hv.2 s hs,hu.2 s hs]
open Rubik RubikGeometry RubikExceptional

private theorem RubikExceptional.cross_solves_inverse {n : ℕ} {a b : Fin n} {τ : Equiv.Perm (Fin 24)}
    {w : List (Move n)} (hw : CrossSolves a b τ w) :
    CrossSolves a b τ⁻¹ (inverseWord w) := by
  constructor
  · intro i
    rw [word_inverse]
    apply (wordPerm w).injective
    simp [hw.1]
  · intro s hs
    rw [word_inverse]
    apply (wordPerm w).injective
    simp [hw.2 s hs]

private theorem RubikExceptional.cross_solves_mul {n : ℕ} {a b : Fin n} {σ τ : Equiv.Perm (Fin 24)}
    {u v : List (Move n)} (hu : CrossSolves a b σ u) (hv : CrossSolves a b τ v) :
    CrossSolves a b (σ * τ) (v ++ u) := by
  constructor
  · intro i
    simp only [word_append,Equiv.Perm.mul_apply,hu.1,hv.1]
  · intro s hs
    simp only [word_append,Equiv.Perm.mul_apply,hv.2 s hs,hu.2 s hs]

open Rubik RubikGeometry RubikExceptional Equiv.Perm

noncomputable section

private def crossPrimitiveWord {n : ℕ} (a b : Fin n) : List (Move n) :=
  let X := genMove a b 6
  let F := genMove a b 5
  let Z := genMove a b 7
  [inverseMove Z, X, inverseMove F, inverseMove X, Z, X, F, inverseMove X]

private theorem crossPrimitiveWord_perm {n : ℕ} (a b : Fin n) :
    wordPerm (crossPrimitiveWord a b) = commElt a b := by
  simp only [crossPrimitiveWord,wordPerm,List.map_cons,List.map_nil,List.reverse_cons,List.reverse_nil,
    List.prod_append,List.prod_cons,List.prod_nil,one_mul,mul_one,inverse_move_perm,
    commElt,mul_inv_rev,inv_inv]
  simp only [mul_assoc]

private theorem crossPrimitiveWord_solves {n : ℕ} (a b : Fin n) (ha : Regular n a) (hb : b.rev=b) :
    CrossSolves a b crossThreeCycle (crossPrimitiveWord a b) := by
  constructor
  · intro i
    rw [crossPrimitiveWord_perm]
    exact cross_comm_lab ha hb i
  · intro s hs
    rw [crossPrimitiveWord_perm]
    exact cross_comm_off ha hb s hs

private theorem cross_solves_conjugate {n : ℕ} {a b : Fin n} (ha : Regular n a) (hb : b.rev=b)
    (k : Fin 9) (τ : Equiv.Perm (Fin 24)) (w : List (Move n))
    (hw : CrossSolves a b τ w) :
    CrossSolves a b (crossControl k * τ * (crossControl k)⁻¹)
      ([inverseMove (crossControlMove a k)] ++ w ++ [crossControlMove a k]) := by
  let P := movePermutation (crossControlMove a k)
  have hmove (i : Fin 24) : P (lab a b i) = lab a b (crossControl k i) := cross_control_lab ha hb k i
  have hinv (i : Fin 24) : P⁻¹ (lab a b i) = lab a b ((crossControl k)⁻¹ i) :=
    inverse_on_labels _ _ _ hmove i
  have hperm : wordPerm ([inverseMove (crossControlMove a k)] ++ w ++ [crossControlMove a k]) =
      P * wordPerm w * P⁻¹ := by
    rw [word_append,word_append,word_singleton,word_singleton,inverse_move_perm]
    simp [P,mul_assoc]
  rw [CrossSolves]
  refine ⟨?_,?_⟩
  · intro i
    rw [hperm]
    simp only [Equiv.Perm.mul_apply,hinv,hw.1,hmove]
  · intro s hs
    have hs' : P⁻¹ s ∉ Set.range (lab a b) := by
      rintro ⟨i,hi⟩
      apply hs
      refine ⟨crossControl k i,?_⟩
      rw [← hmove, hi]
      exact P.apply_symm_apply s
    rw [hperm]
    change P (wordPerm w (P⁻¹ s)) = s
    rw [hw.2 _ hs']
    exact P.apply_symm_apply s

private theorem cross_uniform_alternating_single (τ : Equiv.Perm (Fin 24))
    (hτ : τ ∈ alternatingGroup (Fin 24)) :
    ∃ K : ℕ, ∀ (n : ℕ) (a b : Fin n), Regular n a → b.rev=b →
      ∃ w : List (Move n), w.length ≤ K ∧ CrossSolves a b τ w := by
  classical
  let H : Subgroup (Equiv.Perm (Fin 24)) :=
    { carrier := {τ | ∃ K : ℕ, ∀ (n : ℕ) (a b : Fin n), Regular n a → b.rev=b →
        ∃ w : List (Move n), w.length ≤ K ∧ CrossSolves a b τ w}
      one_mem' := by
        refine ⟨0,?_⟩
        intro n a b ha hb
        exact ⟨[],by simp, by constructor <;> simp [wordPerm]⟩
      mul_mem' := by
        rintro σ τ ⟨K,hK⟩ ⟨L,hL⟩
        refine ⟨K+L,?_⟩
        intro n a b ha hb
        obtain ⟨u,hu,hU⟩ := hK n a b ha hb
        obtain ⟨v,hv,hV⟩ := hL n a b ha hb
        refine ⟨v++u,?_,cross_solves_mul hU hV⟩
        simp only [List.length_append]
        omega
      inv_mem' := by
        rintro τ ⟨K,hK⟩
        refine ⟨K,?_⟩
        intro n a b ha hb
        obtain ⟨w,hw,hW⟩ := hK n a b ha hb
        exact ⟨inverseWord w,by simpa using hw,cross_solves_inverse hW⟩ }
  have h0 : crossThreeCycle ∈ H := by
    refine ⟨8,?_⟩
    intro n a b ha hb
    exact ⟨crossPrimitiveWord a b,by simp [crossPrimitiveWord],crossPrimitiveWord_solves a b ha hb⟩
  have hconj (k : Fin 9) (σ : Equiv.Perm (Fin 24)) (hσ : σ ∈ H) :
      crossControl k * σ * (crossControl k)⁻¹ ∈ H := by
    obtain ⟨K,hK⟩ := hσ
    refine ⟨K+2,?_⟩
    intro n a b ha hb
    obtain ⟨w,hw,hW⟩ := hK n a b ha hb
    refine ⟨[inverseMove (crossControlMove a k)] ++ w ++ [crossControlMove a k],?_,
      cross_solves_conjugate ha hb k σ w hW⟩
    simp only [List.length_append,List.length_singleton]
    omega
  have hn : Subgroup.closure (Set.range crossControl) ≤ Subgroup.normalizer (H : Set _) := by
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨k,rfl⟩
    exact Subgroup.mem_normalizer_fintype (hconj k)
  rw [cross_control_top] at hn
  have hA : alternatingGroup (Fin 24) ≤ H := by
    rw [← closure_three_cycles_eq_alternating]
    apply (Subgroup.closure_le _).mpr
    intro c hc
    have ht : crossThreeCycle.IsThreeCycle := by
      apply card_support_eq_three_iff.mp
      decide
    have hj : IsConj crossThreeCycle c := isConj_iff_cycleType_eq.mpr (ht.trans hc.symm)
    obtain ⟨g,hg⟩ := isConj_iff.mp hj
    rw [← hg]
    exact (Subgroup.mem_normalizer_iff.mp (hn (Subgroup.mem_top g)) crossThreeCycle).mp h0
  exact hA hτ

private theorem RubikExceptional.cross_uniform_alternating :
    ∃ C : ℕ, ∀ (n : ℕ) (a b : Fin n), Regular n a → b.rev=b →
      ∀ τ ∈ alternatingGroup (Fin 24), ∃ w : List (Move n),
        w.length ≤ C ∧ CrossSolves a b τ w := by
  classical
  have hchoice (τ : alternatingGroup (Fin 24)) :
      ∃ K : ℕ, ∀ (n : ℕ) (a b : Fin n), Regular n a → b.rev=b →
        ∃ w : List (Move n), w.length ≤ K ∧ CrossSolves a b τ.val w :=
    cross_uniform_alternating_single τ.val τ.property
  choose bound hbound using hchoice
  refine ⟨Finset.univ.sup bound,?_⟩
  intro n a b ha hb τ hτ
  obtain ⟨w,hw,hW⟩ := hbound ⟨τ,hτ⟩ n a b ha hb
  exact ⟨w,hw.trans (Finset.le_sup (f := bound) (Finset.mem_univ (⟨τ,hτ⟩ : alternatingGroup (Fin 24)))),hW⟩

open Rubik RubikGeometry RubikOrbit
set_option maxHeartbeats 1000000

private theorem RubikOrbit.rigid_lab {n : ℕ} (a b : Fin n) (ax : Rubik.Axis) (i : Fin 24) :
    Rubik.surfaceRotation n ax (RubikGeometry.lab a b i) =
      RubikGeometry.lab a b (RubikOrbit.rigidLabelPermutation ax i) := by
  have revlo : (lo a).rev = hi a := by
    apply Fin.ext
    simp [lo, hi, Fin.rev] <;> omega
  have revhi : (hi a).rev = lo a := by
    apply Fin.ext
    simp [lo, hi, Fin.rev] <;> omega
  fin_cases ax <;> fin_cases i <;> apply Subtype.ext <;>
    simp [surfaceRotation, rawRotation, coordinateRotation, normalRotation,
      normalForward, lab, rawLab, posTable, normalTable, rigidLabelPermutation,
      rigid0, rigid1, rigid2, revlo, revhi]

private theorem RubikOrbit.finite_perm_invariant {X : Type*} [Finite X]
    (p : Equiv.Perm X) (S : Set X) (h : Set.MapsTo p S S) (x : X) :
    p x ∈ S ↔ x ∈ S := by
  let f : S → S := fun s => ⟨p s, h s.property⟩
  have hf : Function.Injective f := by
    intro s t he
    apply Subtype.ext
    exact p.injective (congrArg Subtype.val he)
  have hs : Function.Surjective f := Finite.surjective_of_injective hf
  constructor
  · intro hx
    obtain ⟨y, hy⟩ := hs ⟨p x, hx⟩
    have he : p y.val = p x := congrArg Subtype.val hy
    exact p.injective he ▸ y.property
  · exact fun hx => h hx

private theorem RubikOrbit.slice_invariant {n : ℕ} (a b : Fin n) (ax : Rubik.Axis)
    (l : Fin n) (s : Rubik.Sticker n) :
    Rubik.sliceQuarter n ax l s ∈ Set.range (RubikGeometry.lab a b) ↔
      s ∈ Set.range (RubikGeometry.lab a b) := by
  apply RubikOrbit.finite_perm_invariant
  rintro s ⟨i, rfl⟩
  by_cases h : coordinate (lab a b i).val.1 ax = l
  · refine ⟨rigidLabelPermutation ax i, ?_⟩
    simpa only [sliceQuarter, Equiv.coe_fn_mk, h, if_true] using
      (RubikOrbit.rigid_lab a b ax i).symm
  · exact ⟨i, by simp only [sliceQuarter, Equiv.coe_fn_mk, h, if_false]⟩

private theorem RubikOrbit.move_invariant {n : ℕ} (a b : Fin n)
    (m : Rubik.Move n) (s : Rubik.Sticker n) :
    Rubik.movePermutation m s ∈ Set.range (RubikGeometry.lab a b) ↔
      s ∈ Set.range (RubikGeometry.lab a b) := by
  have hp (j : ℕ) (s : Sticker n) :
      (sliceQuarter n m.1 m.2.1 ^ j) s ∈ Set.range (lab a b) ↔
        s ∈ Set.range (lab a b) := by
    induction j generalizing s with
    | zero => simp
    | succ j ih =>
      rw [pow_succ, Equiv.Perm.mul_apply, ih,
        RubikOrbit.slice_invariant a b m.1 m.2.1]
  exact hp _ s

private theorem RubikOrbit.perm_on_labels {X V : Type*} [Finite V]
    (f : V → X) (hf : Function.Injective f) (p : Equiv.Perm X)
    (h : Set.MapsTo p (Set.range f) (Set.range f)) :
    ∃ σ : Equiv.Perm V, ∀ i, p (f i) = f (σ i) := by
  classical
  have hex (i : V) : ∃ j, f j = p (f i) := h ⟨i, rfl⟩
  choose g hg using hex
  have hginj : Function.Injective g := by
    intro i j he
    apply hf
    apply p.injective
    rw [← hg i, ← hg j, he]
  exact ⟨Equiv.ofBijective g ⟨hginj, Finite.surjective_of_injective hginj⟩,
    fun i => (hg i).symm⟩

private theorem RubikOrbit.reachable_colours_of_injective {n : ℕ} {a b : Fin n} (hf : Function.Injective (RubikGeometry.lab a b)) (c : Rubik.Colouring n) (hc : Rubik.Reachable c) : ∃ σ : Equiv.Perm (Fin 24), c ∘ RubikGeometry.lab a b = RubikGeometry.normalTable ∘ σ := by
  let Q : Colouring n → Prop := fun c =>
    ∃ σ : Equiv.Perm (Fin 24), c ∘ lab a b = normalTable ∘ σ
  have hstep (m : Move n) (c : Colouring n) (hc : Q c) : Q (applyMove m c) := by
    have hp : Set.MapsTo ((movePermutation m)⁻¹ : Equiv.Perm (Sticker n)) (Set.range (lab a b))
        (Set.range (lab a b)) := by
      intro s hs
      apply (RubikOrbit.move_invariant a b m ((movePermutation m)⁻¹ s)).mp
      simpa using hs
    obtain ⟨τ, hτ⟩ := RubikOrbit.perm_on_labels (lab a b) hf (movePermutation m)⁻¹ hp
    obtain ⟨σ, hσ⟩ := hc
    refine ⟨σ * τ, ?_⟩
    funext i
    change c ((movePermutation m)⁻¹ (lab a b i)) = normalTable (σ (τ i))
    rw [hτ]
    exact congrFun hσ (τ i)
  have hword (w : List (Move n)) (c : Colouring n) (hc : Q c) : Q (applyWord w c) := by
    induction w generalizing c with
    | nil => exact hc
    | cons m w ih => exact ih (applyMove m c) (hstep m c hc)
  obtain ⟨w, rfl⟩ := hc
  exact hword w (solved n) ⟨1, rfl⟩

open Equiv.Perm

private theorem RubikChannel.Colour.alternating_transitive {V Colour : Type*} [Fintype V] [DecidableEq V] (κ : V → Colour)
    (ρ : Equiv.Perm V) (hρ : sign ρ = -1) (hκ : κ ∘ ρ = κ)
    (x y : RubikChannel.Colour.Orbit κ) :
    ∃ σ ∈ alternatingGroup V, RubikChannel.Colour.orbitAction κ σ x = y := by
  have evenRep (f : RubikChannel.Colour.Orbit κ) :
      ∃ σ ∈ alternatingGroup V, f.val = κ ∘ σ := by
    obtain ⟨σ, hσ⟩ := f.property
    rcases Int.units_eq_one_or (sign σ) with hs | hs
    · exact ⟨σ, mem_alternatingGroup.mpr hs, hσ⟩
    · refine ⟨ρ * σ, mem_alternatingGroup.mpr (by simp [hρ, hs]), ?_⟩
      rw [hσ]
      funext i
      exact (congrFun hκ (σ i)).symm
  obtain ⟨σ, hσ, hx⟩ := evenRep x
  obtain ⟨τ, hτ, hy⟩ := evenRep y
  refine ⟨τ⁻¹ * σ, (alternatingGroup V).mul_mem ((alternatingGroup V).inv_mem hτ) hσ, ?_⟩
  apply Subtype.ext
  funext i
  change x.val ((τ⁻¹ * σ)⁻¹ i) = y.val i
  rw [hx, hy]
  simp [Function.comp_def]

open Rubik RubikGeometry RubikExceptional

theorem proof_RubikExceptional_CrossUniformColoured :
    ∃ C : ℕ, ∀ (n : ℕ) (a b : Fin n), Regular n a → b.rev=b →
      ∀ (c d : Colouring n), Reachable c → Reachable d →
        ∃ w : List (Move n), w.length ≤ C ∧
          (∀ i, applyWord w c (lab a b i) = d (lab a b i)) ∧
          (∀ s, s ∉ Set.range (lab a b) → wordPerm w s = s) := by
  obtain ⟨C,hC⟩ := RubikExceptional.cross_uniform_alternating
  refine ⟨C,?_⟩
  intro n a b ha hb c d hc hd
  obtain ⟨σ,hσ⟩ := RubikOrbit.reachable_colours_of_injective (cross_injective ha hb) c hc
  obtain ⟨τ,hτ⟩ := RubikOrbit.reachable_colours_of_injective (cross_injective ha hb) d hd
  let x : RubikChannel.Colour.Orbit normalTable := ⟨c ∘ lab a b,σ,hσ⟩
  let y : RubikChannel.Colour.Orbit normalTable := ⟨d ∘ lab a b,τ,hτ⟩
  obtain ⟨p,hp,hxy⟩ := RubikChannel.Colour.alternating_transitive normalTable
    (Equiv.swap (0 : Fin 24) 1) (Equiv.Perm.sign_swap (by decide)) (by decide) x y
  obtain ⟨w,hw,hW⟩ := hC n a b ha hb p hp
  refine ⟨w,hw,?_,hW.2⟩
  intro i
  rw [applyWord_wordPerm]
  change c ((wordPerm w)⁻¹ (lab a b i)) = d (lab a b i)
  rw [inverse_on_labels _ _ _ hW.1]
  exact congrArg (fun f : RubikChannel.Colour.Orbit normalTable => f.val i) hxy
