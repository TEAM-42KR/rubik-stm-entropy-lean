import RubikSTM.Definitions.Rectangles.PayloadInterface
set_option autoImplicit false

namespace RubikRectangle
open RubikPayload

def rawHom : Pair →* Equiv.Perm Data where
  toFun := rawAction
  map_one' := by ext x i <;> rfl
  map_mul' g h := by ext x i <;> rfl

def program {n L t : ℕ} (ws : Fin L → Fin t → List (Rubik.Move n)) : List (Rubik.Move n) :=
  (List.ofFn (fun i => (List.ofFn (ws i)).flatten)).flatten

def Framed {n L t : ℕ} (X Y : Finset (Fin n))
    (owner : X → Fin t) (F : Fin L → X → Y → Pair)
    (ws : Fin L → Fin t → List (Rubik.Move n)) : Prop :=
  (∀ (a : X) (b : Y) (hb : 0 < b.val.val ∧ b.val.val + 1 < n)
      (i : Fin L) (j : Fin t),
    ActsPair a.val b.val hb (ws i j) (if j = owner a then F i a b else B)) ∧
    ∀ (i : Fin L) (j : Fin t) (s : Rubik.Sticker n), ¬ Rectangles X Y s →
      RubikBand.wordPerm (ws i j) s = columnBaseline Y s

end RubikRectangle
