import RubikSTM.Definitions.Geometry.StmGraph
set_option autoImplicit false

namespace RubikOBTM

abbrev BlockMove (n : ℕ) := Rubik.Axis × Bool × Fin (n - 1) × Fin 3

def width {n : ℕ} (m : BlockMove n) : ℕ := m.2.2.1.val + 1

def selected {n : ℕ} (a : Rubik.Axis) (side : Bool) (k : Fin (n - 1))
    (l : Fin n) : Prop :=
  if side then n - (k.val + 1) ≤ l.val else l.val < k.val + 1

instance selectedDecidable {n : ℕ} (a : Rubik.Axis) (side : Bool)
    (k : Fin (n - 1)) (l : Fin n) : Decidable (selected a side k l) := by
  unfold selected
  infer_instance

def blockQuarter (n : ℕ) (a : Rubik.Axis) (side : Bool) (k : Fin (n - 1)) :
    Equiv.Perm (Rubik.Sticker n) where
  toFun := fun s => if selected a side k (Rubik.coordinate s.val.1 a)
    then Rubik.surfaceRotation n a s else s
  invFun := fun s => if selected a side k (Rubik.coordinate s.val.1 a)
    then (Rubik.surfaceRotation n a).symm s else s
  left_inv := by
    intro s
    have hf : ∀ t : Rubik.Sticker n,
        Rubik.coordinate (Rubik.surfaceRotation n a t).val.1 a =
          Rubik.coordinate t.val.1 a := by
      intro t
      fin_cases a <;>
        simp [Rubik.surfaceRotation, Rubik.rawRotation, Rubik.coordinateRotation, Rubik.coordinate]
    have hb : ∀ t : Rubik.Sticker n,
        Rubik.coordinate ((Rubik.surfaceRotation n a).symm t).val.1 a =
          Rubik.coordinate t.val.1 a := by
      intro t
      simpa only [Equiv.apply_symm_apply] using (hf ((Rubik.surfaceRotation n a).symm t)).symm
    by_cases h : selected a side k (Rubik.coordinate s.val.1 a)
    · simp [h, hf]
    · simp [h]
  right_inv := by
    intro s
    have hf : ∀ t : Rubik.Sticker n,
        Rubik.coordinate (Rubik.surfaceRotation n a t).val.1 a =
          Rubik.coordinate t.val.1 a := by
      intro t
      fin_cases a <;>
        simp [Rubik.surfaceRotation, Rubik.rawRotation, Rubik.coordinateRotation, Rubik.coordinate]
    have hb : ∀ t : Rubik.Sticker n,
        Rubik.coordinate ((Rubik.surfaceRotation n a).symm t).val.1 a =
          Rubik.coordinate t.val.1 a := by
      intro t
      simpa only [Equiv.apply_symm_apply] using (hf ((Rubik.surfaceRotation n a).symm t)).symm
    by_cases h : selected a side k (Rubik.coordinate s.val.1 a)
    · simp [h, hb]
    · simp [h]

def blockPermutation {n : ℕ} (m : BlockMove n) : Equiv.Perm (Rubik.Sticker n) :=
  blockQuarter n m.1 m.2.1 m.2.2.1 ^ (m.2.2.2.val + 1)

def applyBlock {n : ℕ} (m : BlockMove n) (c : Rubik.Colouring n) : Rubik.Colouring n :=
  fun s => c ((blockPermutation m).symm s)

def applyBlockWord {n : ℕ} (w : List (BlockMove n)) (c : Rubik.Colouring n) :
    Rubik.Colouring n := w.foldl (fun state m => applyBlock m state) c

def BlockReachable {n : ℕ} (c : Rubik.Colouring n) : Prop :=
  ∃ w : List (BlockMove n), applyBlockWord w (Rubik.solved n) = c

def obtmGraph (n : ℕ) : SimpleGraph (Rubik.Position n) where
  Adj c d := c ≠ d ∧
    ((∃ m : BlockMove n, applyBlock m c.val = d.val) ∨
      (∃ m : BlockMove n, applyBlock m d.val = c.val))
  symm := ⟨by
    intro c d h
    exact ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨by intro c h; exact h.1 rfl⟩

noncomputable def obtmDiameter (n : ℕ) : ℕ := (obtmGraph n).diam

noncomputable def normalizedDiameter (n : ℕ) : ℝ :=
  (obtmDiameter n : ℝ) * Real.log (n : ℝ) / (n : ℝ) ^ 2

def blockSliceWord {n : ℕ} (m : BlockMove n) : List (Rubik.Move n) :=
  ((List.finRange n).filter (fun l => selected m.1 m.2.1 m.2.2.1 l)).map
    (fun l => (m.1, l, m.2.2.2))

end RubikOBTM
