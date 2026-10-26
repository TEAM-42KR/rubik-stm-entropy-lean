import Mathlib
import RubikSTM.Definitions.Payloads.Realizes
import RubikSTM.Lemmas.Payloads.InverseWordPermutation
import RubikSTM.Lemmas.Payloads.BaselineAction
import RubikSTM.Lemmas.Payloads.RectanglesBands
import RubikSTM.Lemmas.Payloads.BaselinePhysical
import RubikSTM.Lemmas.Bands.WordBand
set_option autoImplicit false

theorem proof_RubikPayload_conjugatePayload {n : ℕ} {A Y : Finset (Fin n)} (h : RubikPayload.Admissible A Y)
  (g : Fin n → RubikPayload.Pair) (σ : Fin n → Equiv.Perm (Fin 24))
  (U : List (Rubik.Move n))
  (hfix : ∀ s : Rubik.Sticker n, ¬ RubikBand.Bands A s → RubikBand.wordPerm U s = s)
  (hact : ∀ a ∈ A, ∀ b ∈ Y, ∀ hb : 0 < b.val ∧ b.val + 1 < n, ∀ i,
    RubikBand.wordPerm U (RubikGeometry.lab a b i) = RubikGeometry.lab a b (σ a i) ∧
    RubikBand.wordPerm U (RubikOrbit.minusLab a b hb i) =
      RubikOrbit.minusLab a b hb (σ a i))
  (hconj : ∀ a ∈ A, σ a * RubikGeometry.gen7 * (σ a)⁻¹ = (g a).1 ∧
    σ a * RubikOrbit.minusB * (σ a)⁻¹ = (g a).2) :
  RubikPayload.Realizes A Y g
    (RubikPayload.inverseWord U ++ RubikPayload.baselineWord Y ++ U) := by
  let u := RubikBand.wordPerm U
  let Z := RubikPayload.columnBaseline Y
  have cat (v w : List (Rubik.Move n)) : RubikBand.wordPerm (v++w) =
      RubikBand.wordPerm w * RubikBand.wordPerm v := by
    simp [RubikBand.wordPerm, List.reverse_append]
  have hword : RubikBand.wordPerm (RubikPayload.inverseWord U ++ RubikPayload.baselineWord Y ++ U) =
      u * Z * u⁻¹ := by
    rw [cat, cat, (RubikPayload.inverseWordPermutation U).1]
    rfl
  have lift (lab : Fin 24 → Rubik.Sticker n) (σ β γ : Equiv.Perm (Fin 24))
      (hu : ∀ i, u (lab i) = lab (σ i)) (hz : ∀ i, Z (lab i) = lab (β i))
      (hc : σ * β * σ⁻¹ = γ) : ∀ i, (u * Z * u⁻¹) (lab i) = lab (γ i) := by
    intro i
    have hi : u⁻¹ (lab i) = lab (σ⁻¹ i) := by
      apply u.injective
      rw [show u (u⁻¹ (lab i)) = lab i from Equiv.apply_symm_apply u _, hu]
      exact congrArg lab (Equiv.apply_symm_apply σ i).symm
    change u (Z (u⁻¹ (lab i))) = lab (γ i)
    rw [hi, hz, hu]
    exact congrArg lab (congrArg (fun p : Equiv.Perm (Fin 24) => p i) hc)
  constructor
  · intro a ha b hbY hb i
    rw [hword]
    exact ⟨lift (RubikGeometry.lab a b) (σ a) RubikGeometry.gen7 (g a).1
      (fun j => (hact a ha b hbY hb j).1)
      (fun j => (RubikPayload.baselineAction h ha hbY hb j).1) (hconj a ha).1 i,
      lift (RubikOrbit.minusLab a b hb) (σ a) RubikOrbit.minusB (g a).2
      (fun j => (hact a ha b hbY hb j).2)
      (fun j => (RubikPayload.baselineAction h ha hbY hb j).2) (hconj a ha).2 i⟩
  · intro s hs
    rw [hword]
    change u (Z (u⁻¹ s)) = Z s
    have cancel : u (u⁻¹ s) = s := Equiv.apply_symm_apply u s
    have hs' : ¬ (RubikBand.Bands A s ∧ RubikBand.Bands Y s) := by
      intro hh; exact hs ((RubikPayload.rectanglesBands h s).mpr hh)
    have hbandI (c : Fin n) : RubikBand.Band c (u⁻¹ s) ↔ RubikBand.Band c s := by
      have H := RubikBand.wordBand c U (u⁻¹ s)
      change RubikBand.Band c (u (u⁻¹ s)) ↔ _ at H
      rw [cancel] at H
      exact H.symm
    by_cases hA : RubikBand.Bands A s
    · have hY : ¬ RubikBand.Bands Y s := by intro hy; exact hs' ⟨hA,hy⟩
      have hYi : ¬ RubikBand.Bands Y (u⁻¹ s) := by
        rintro ⟨c,hc,hcs⟩
        exact hY ⟨c,hc,(hbandI c).mp hcs⟩
      have hzI : Z (u⁻¹ s) = u⁻¹ s := (RubikPayload.baselinePhysical Y).2 _ hYi
      have hzS : Z s = s := (RubikPayload.baselinePhysical Y).2 _ hY
      rw [hzI, cancel, hzS]
    · have hu : u s = s := hfix s hA
      have hui : u⁻¹ s = s := by
        apply u.injective
        rw [cancel]
        exact hu.symm
      have hZA : ¬ RubikBand.Bands A (Z s) := by
        rintro ⟨c,hc,hcs⟩
        exact hA ⟨c,hc,(RubikBand.wordBand c (RubikPayload.baselineWord Y) s).mp hcs⟩
      have huz : u (Z s) = Z s := hfix _ hZA
      rw [hui, huz]

#print axioms proof_RubikPayload_conjugatePayload
