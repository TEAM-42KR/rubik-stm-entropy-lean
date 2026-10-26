import Mathlib
import RubikSTM.Definitions.Channel.Transition
set_option autoImplicit false

noncomputable section
open scoped Matrix.Norms.L2Operator BigOperators

namespace RubikOBTM.Spectral

def Fixed {G X : Type*} [Group G] (act : G →* Equiv.Perm X)
    (K : Subgroup G) (v : X → ℝ) : Prop := ∀ g ∈ K, ∀ x, v (act g x) = v x

def RelativeSurjective {G C : Type*} [Group G] (K : Subgroup G) (letter : C → G) : Prop :=
  ∀ g ∈ K, ∃ c d, letter c * (letter d)⁻¹ = g

def phaseKernel {G C X : Type*} [Group G] [Fintype C] [Fintype X]
    (act : G →* Equiv.Perm X) (μ : RubikJanson.FiniteLaw C)
    (letter : C → G) (n : G) : Matrix X X ℝ :=
  RubikChannel.transition μ (fun c => act (n * letter c))

def pairAction {G X : Type*} [Group G] (act : G →* Equiv.Perm X) :
    (G × G) →* Equiv.Perm (X × X) where
  toFun g := (act g.1).prodCongr (act g.2)
  map_one' := by ext x <;> simp
  map_mul' g h := by ext x <;> simp [Equiv.Perm.mul_apply]

def doubleLetter {G C : Type*} [Group G] (letter : C → G) (independent : Bool) :
    C × C → G × G :=
  fun c => if independent then (letter c.1,letter c.2) else (letter c.1,letter c.1)

def diagonal {G : Type*} [Group G] (K : Subgroup G) : Subgroup (G × G) :=
  { carrier := {g | g.1 ∈ K ∧ g.2=g.1}
    one_mem' := by simp
    mul_mem' := by rintro g h ⟨hg,he⟩ ⟨hh,hf⟩; exact ⟨K.mul_mem hg hh,by simp [he,hf]⟩
    inv_mem' := by rintro g ⟨hg,he⟩; exact ⟨K.inv_mem hg,by simp [he]⟩ }

def doubleGroup {G : Type*} [Group G] (K : Subgroup G) (independent : Bool) : Subgroup (G × G) :=
  if independent then K.prod K else diagonal K

def period {X : Type*} [Fintype X] [DecidableEq X] {T : ℕ}
    (A : Fin T → Matrix X X ℝ) : Matrix X X ℝ := (List.ofFn A).prod

def averaging {X : Type*} [Fintype X] : Matrix X X ℝ :=
  fun _ _ => (Fintype.card X : ℝ)⁻¹

end RubikOBTM.Spectral
