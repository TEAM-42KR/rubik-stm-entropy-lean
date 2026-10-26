import RubikSTM.Definitions.Rectangles.PayloadInterface
import RubikSTM.Lemmas.Orbits.ReachableColours
import RubikSTM.Lemmas.Orbits.FlipLabel
set_option autoImplicit false

open RubikRectangle

theorem proof_RubikRectangle_reachable_view {n : ℕ} {a b : Fin n} (hg : RubikGeometry.Generic n a b)
    (hb : 0 < b.val ∧ b.val + 1 < n) (c : Rubik.Position n) :
    ∃ x : RubikChannel.Paired.State, data x = view c.val a b hb := by
  have hswap : RubikGeometry.Generic n b a :=
    ⟨hg.one_le_b,hg.one_le_a,hg.b_small,hg.a_small,Ne.symm hg.ne⟩
  obtain ⟨σ,hσ⟩ := RubikOrbit.reachable_colours hg c.val c.property
  obtain ⟨τ,hτ⟩ := RubikOrbit.reachable_colours hswap c.val c.property
  refine ⟨(⟨c.val ∘ RubikGeometry.lab a b,⟨σ,hσ⟩⟩,
    ⟨c.val ∘ RubikOrbit.minusLab a b hb,⟨τ * RubikOrbit.swapPhi,?_⟩⟩),rfl⟩
  funext i
  rw [Function.comp_apply, RubikOrbit.flipLabel hg hb]
  exact congrFun hτ (RubikOrbit.swapPhi i)

#print axioms proof_RubikRectangle_reachable_view
