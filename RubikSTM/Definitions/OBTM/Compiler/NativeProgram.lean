import RubikSTM.Definitions.OBTM.Band.SlabWord
import RubikSTM.Definitions.OBTM.Global.RectangleCompiler
import RubikSTM.Definitions.Rectangles.Framed
import RubikSTM.Definitions.OBTM.Compiler.NativeCoalescedWord
set_option autoImplicit false

namespace RubikOBTMCompiler

def nativeProgram {n L t : ℕ} (ws : Fin L → Fin t → List (RubikOBTM.BlockMove n)) :
    List (RubikOBTM.BlockMove n) :=
  (List.ofFn (fun i => (List.ofFn (ws i)).flatten)).flatten

def commonView {n : ℕ} (c : Rubik.Colouring n) (a b : Fin n) : RubikRectangle.Data :=
  (c ∘ RubikOBTM.Band.plus a b, c ∘ RubikOBTM.Band.minus a b)

def NativeActsPair {n : ℕ} (a b : Fin n) (w : List (RubikOBTM.BlockMove n))
    (g : RubikPayload.Pair) : Prop :=
  (∀ i, RubikOBTM.Band.wordPerm w (RubikOBTM.Band.plus a b i) = RubikOBTM.Band.plus a b (g.1 i)) ∧
  ∀ i, RubikOBTM.Band.wordPerm w (RubikOBTM.Band.minus a b i) = RubikOBTM.Band.minus a b (g.2 i)

structure OddLayout {n : ℕ} (X : Finset (Fin n)) (k : ℕ) where
  blocks : ℕ
  blocks_eq : blocks = RubikRectangle.rowCeil X.card k + oddPad (RubikRectangle.rowCeil X.card k)
  owner : Fin n → Fin blocks
  row : Fin n → Fin k
  injective : ∀ a ∈ X, ∀ b ∈ X, owner a = owner b → row a = row b → a = b

def OddLayout.rows {n k : ℕ} {X : Finset (Fin n)} (P : OddLayout X k)
    (j : Fin P.blocks) : Finset (Fin n) := X.filter (fun a => P.owner a = j)

def halfPair : RubikPayload.Pair := (RubikOBTM.Band.actualSlabPlus^2, RubikOBTM.Band.actualSlabMinus^2)

def cellBaseline {n : ℕ} (Y : Finset (Fin n)) (b : Fin n) : RubikPayload.Pair :=
  halfPair ^ (Y.filter (fun d => b ≤ d)).card

noncomputable def cutBaseline {n : ℕ} (Y B : Finset (Fin n)) : Equiv.Perm (Rubik.Sticker n) :=
  if h : Y.Nonempty then
    (B.toList.map (fun b => RubikOBTM.Band.slabPerm (Y.min' h) b ^ 2)).reverse.prod
  else 1

noncomputable def fullBaseline {n : ℕ} (Y : Finset (Fin n)) : Equiv.Perm (Rubik.Sticker n) :=
  cutBaseline Y Y

def NativePulseInterface (C : ℕ) : Prop :=
  ∀ {n : ℕ} (A Y : Finset (Fin n)), RubikPayload.Admissible A Y →
    Set.OrdConnected (Y : Set (Fin n)) →
    ∀ (p : RubikOBTM.Finite.Phase) (g : Fin n → RubikOBTM.Finite.Intrinsic),
      (∀ a ∈ A, g a ∈ RubikOBTM.Finite.nativeC) →
      ∀ B : Finset (Fin n), B ⊆ Y →
      ∃ w : List (RubikOBTM.BlockMove n),
        w.length ≤ B.card + C * (A.card + 1) ∧
        (∀ a ∈ A, ∀ b ∈ Y,
          NativeActsPair a b w
            ((RubikOBTM.Finite.inclusion (RubikOBTM.Finite.phaseHom p (g a))) ^
              (B.filter (fun d => b ≤ d)).card)) ∧
        ∀ s : Rubik.Sticker n, ¬ RubikPayload.Rectangles A Y s →
          RubikOBTM.Band.wordPerm w s = cutBaseline Y B s

end RubikOBTMCompiler
