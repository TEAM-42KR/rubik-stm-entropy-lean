import Mathlib
import RubikSTM.Lemmas.WordConstruction.BaselineRestriction
import RubikSTM.Lemmas.WordConstruction.PowModFour
set_option autoImplicit false

theorem proof_RubikCompiler_exteriorCancellation {G X : Type*} [Group G] [MulAction G X]
  (Z : G) (hZ : Z ^ 4 = 1) (S : Set X)
  (hInv : ∀ x ∈ S, Z • x ∈ S) (layers : List (List G))
  (ht : ∀ bs ∈ layers, bs.length % 4 = 1)
  (hblock : ∀ bs ∈ layers, ∀ f ∈ bs, ∀ x ∈ S, f • x = Z • x)
  (hL : layers.length % 4 = 0) :
  ∀ x ∈ S, (layers.map (fun bs => bs.reverse.prod)).reverse.prod • x = x := by
  have hlayer : ∀ g ∈ layers.map (fun bs => bs.reverse.prod),
      ∀ x ∈ S, g • x = Z • x := by
    intro g hg x hx
    obtain ⟨bs, hbs, rfl⟩ := List.mem_map.mp hg
    rw [RubikCompiler.baselineRestriction Z S hInv bs (hblock bs hbs) x hx,
      RubikCompiler.powModFour Z hZ, ht bs hbs, pow_one]
  intro x hx
  rw [RubikCompiler.baselineRestriction Z S hInv _ hlayer x hx,
    List.length_map, RubikCompiler.powModFour Z hZ, hL, pow_zero, one_smul]

#print axioms proof_RubikCompiler_exteriorCancellation
