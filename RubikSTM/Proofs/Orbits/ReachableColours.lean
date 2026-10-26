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

theorem proof_RubikOrbit_reachable_colours {n : ℕ} {a b : Fin n}
    (hg : RubikGeometry.Generic n a b) (c : Rubik.Colouring n) (hc : Rubik.Reachable c) :
    ∃ σ : Equiv.Perm (Fin 24), c ∘ RubikGeometry.lab a b = RubikGeometry.normalTable ∘ σ := by
  have hf : Function.Injective (lab a b) := by
    let region (s : RawSticker n) : Bool × Bool × Bool × Normal :=
      (decide (2 * s.1.1.val < n), decide (2 * s.1.2.1.val < n),
        decide (2 * s.1.2.2.val < n), s.2)
    let labelRegion : Fin 24 → Bool × Bool × Bool × Normal := ![
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
    have hlabel : Function.Injective labelRegion := by decide
    have hreg (i : Fin 24) : region (lab a b i).val = labelRegion i := by
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
    intro i j hij
    apply hlabel
    rw [← hreg i, ← hreg j, hij]

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
