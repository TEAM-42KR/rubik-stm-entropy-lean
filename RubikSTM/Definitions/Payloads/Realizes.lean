import RubikSTM.Definitions.Orbits.SwapPhi
import RubikSTM.Definitions.Channel.DisjointFourCycleAlphabet
import RubikSTM.Definitions.Construction.Control.Physical.ActualMoves
set_option autoImplicit false

namespace RubikPayload
abbrev Pair := Equiv.Perm (Fin 24) × Equiv.Perm (Fin 24)

def Half {n : ℕ} (a : Fin n) : Prop := 1 ≤ a.val ∧ 2 * a.val + 2 ≤ n

def Admissible {n : ℕ} (A Y : Finset (Fin n)) : Prop :=
  (∀ a ∈ A, Half a) ∧ (∀ b ∈ Y, Half b) ∧ Disjoint A Y

def Rectangles {n : ℕ} (A Y : Finset (Fin n)) (s : Rubik.Sticker n) : Prop :=
  ∃ a ∈ A, ∃ b ∈ Y,
    s ∈ Set.range (RubikGeometry.lab a b) ∪ Set.range (RubikGeometry.lab b a)

def baselineWord {n : ℕ} (Y : Finset (Fin n)) : List (Rubik.Move n) :=
  (Y.sort (· ≤ ·)).map (fun b => (2,b.rev,0))

def columnBaseline {n : ℕ} (Y : Finset (Fin n)) : Equiv.Perm (Rubik.Sticker n) :=
  RubikBand.wordPerm (baselineWord Y)

def inverseMove {n : ℕ} (m : Rubik.Move n) : Rubik.Move n :=
  (m.1, m.2.1, m.2.2.rev)

def inverseWord {n : ℕ} (w : List (Rubik.Move n)) : List (Rubik.Move n) :=
  w.reverse.map inverseMove

def Realizes {n : ℕ} (A Y : Finset (Fin n)) (g : Fin n → Pair)
    (w : List (Rubik.Move n)) : Prop :=
  (∀ a ∈ A, ∀ b ∈ Y, ∀ hb : 0 < b.val ∧ b.val + 1 < n, ∀ i : Fin 24,
    RubikBand.wordPerm w (RubikGeometry.lab a b i) = RubikGeometry.lab a b ((g a).1 i) ∧
    RubikBand.wordPerm w (RubikOrbit.minusLab a b hb i) =
      RubikOrbit.minusLab a b hb ((g a).2 i)) ∧
  (∀ s : Rubik.Sticker n, ¬ Rectangles A Y s →
    RubikBand.wordPerm w s = columnBaseline Y s)
end RubikPayload
