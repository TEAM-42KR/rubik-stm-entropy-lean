import RubikSTM.Definitions.Payloads.Realizes
import RubikSTM.Definitions.Channel.Paired.P
import RubikSTM.Definitions.Codebook.LayerwiseUnion
set_option autoImplicit false

namespace RubikRectangle
open RubikPayload

def PayloadInterface (C : ℕ) : Prop :=
  ∀ {n : ℕ} (A Y : Finset (Fin n)), Admissible A Y →
    ∀ g : Fin n → Pair,
      (∀ a ∈ A, g a ∈ RubikChannel.disjointFourCycleAlphabet (Fin 24)) →
      ∃ w : List (Rubik.Move n),
        w.length ≤ Y.card + C * (A.card + 1) ∧ Realizes A Y g w

abbrev Data := (Fin 24 → Rubik.Colour) × (Fin 24 → Rubik.Colour)

def data (x : RubikChannel.Paired.State) : Data := (x.1.val, x.2.val)

def rawAction (g : Pair) : Equiv.Perm Data where
  toFun x := (x.1 ∘ g.1.symm, x.2 ∘ g.2.symm)
  invFun x := (x.1 ∘ g.1, x.2 ∘ g.2)
  left_inv x := by ext i <;> simp [Function.comp_def]
  right_inv x := by ext i <;> simp [Function.comp_def]

def view {n : ℕ} (c : Rubik.Colouring n) (a b : Fin n)
    (hb : 0 < b.val ∧ b.val + 1 < n) : Data :=
  (c ∘ RubikGeometry.lab a b, c ∘ RubikOrbit.minusLab a b hb)

def ActsPair {n : ℕ} (a b : Fin n) (hb : 0 < b.val ∧ b.val + 1 < n)
    (w : List (Rubik.Move n)) (g : Pair) : Prop :=
  (∀ i, RubikBand.wordPerm w (RubikGeometry.lab a b i) = RubikGeometry.lab a b (g.1 i)) ∧
    ∀ i, RubikBand.wordPerm w (RubikOrbit.minusLab a b hb i) =
      RubikOrbit.minusLab a b hb (g.2 i)

def rowCeil (m k : ℕ) : ℕ := (m + k - 1) / k

def B : Pair := (RubikGeometry.gen7, RubikOrbit.minusB)

end RubikRectangle
