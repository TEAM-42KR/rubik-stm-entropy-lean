import Mathlib
set_option autoImplicit false

theorem proof_RubikCompiler_baselineRestriction {G X : Type*} [Group G] [MulAction G X]
  (Z : G) (S : Set X) (hInv : ∀ x ∈ S, Z • x ∈ S)
  (blocks : List G)
  (hblock : ∀ f ∈ blocks, ∀ x ∈ S, f • x = Z • x) :
  ∀ x ∈ S, blocks.reverse.prod • x = Z ^ blocks.length • x := by
  revert hblock
  induction blocks with
  | nil => intro hblock x hx; simp
  | cons f fs ih =>
    intro hblock x hx
    have hf : f • x = Z • x := hblock f (by simp) x hx
    have htail : ∀ g ∈ fs, ∀ y ∈ S, g • y = Z • y := by
      intro g hg y hy
      exact hblock g (by simp [hg]) y hy
    calc
      (f :: fs).reverse.prod • x = fs.reverse.prod • (f • x) := by
        simp [List.reverse_cons, mul_smul]
      _ = fs.reverse.prod • (Z • x) := by rw [hf]
      _ = Z ^ fs.length • (Z • x) := ih htail (Z • x) (hInv x hx)
      _ = Z ^ (f :: fs).length • x := by simp [pow_succ, mul_smul]

#print axioms proof_RubikCompiler_baselineRestriction
