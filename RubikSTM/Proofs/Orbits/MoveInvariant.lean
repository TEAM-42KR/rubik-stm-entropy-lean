import RubikSTM.Definitions.Orbits.RigidLabelPermutation
import RubikSTM.Definitions.Channel.Colour.Orbit
set_option autoImplicit false

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

theorem proof_RubikOrbit_move_invariant {n : ℕ} (a b : Fin n)
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
