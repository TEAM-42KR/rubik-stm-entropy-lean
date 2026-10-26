import RubikSTM.Definitions.Wings.Realizes
import RubikSTM.Definitions.Wings.UniformCost
import RubikSTM.Definitions.Bands.Band
set_option autoImplicit false
open Rubik RubikWing

theorem Rubik.sliceQuarter_order_four (n : ℕ) (a : Rubik.Axis) (l : Fin n) : Rubik.sliceQuarter n a l ^ 4 = 1 := by
  apply Equiv.ext
  intro s
  have hf : ∀ t : Rubik.Sticker n,
      Rubik.coordinate (Rubik.surfaceRotation n a t).val.1 a = Rubik.coordinate t.val.1 a := by
    intro t
    fin_cases a <;>
      simp [Rubik.surfaceRotation, Rubik.rawRotation, Rubik.coordinateRotation, Rubik.coordinate]
  change Rubik.sliceQuarter n a l (Rubik.sliceQuarter n a l
    (Rubik.sliceQuarter n a l (Rubik.sliceQuarter n a l s))) = s
  by_cases h : Rubik.coordinate s.val.1 a = l
  · simp only [Rubik.sliceQuarter, Equiv.coe_fn_mk, h, if_true, hf]
    apply Subtype.ext
    rcases s with ⟨⟨⟨x, y, z⟩, b, c⟩, hs⟩
    fin_cases a <;> fin_cases b <;> cases c <;>
      simp [Rubik.surfaceRotation, Rubik.rawRotation, Rubik.coordinateRotation,
        Rubik.normalRotation, Rubik.normalForward]
  · simp [Rubik.sliceQuarter, h]

theorem RubikBand.rotationBand {n : ℕ} (a : Fin n) (q : Rubik.Axis) (s : Rubik.Sticker n) :
  RubikBand.Band a (Rubik.surfaceRotation n q s) ↔ RubikBand.Band a s := by
  fin_cases q <;>
    simp [RubikBand.Band, Fin.exists_fin_succ, Rubik.coordinate,
      Rubik.surfaceRotation, Rubik.rawRotation, Rubik.coordinateRotation,
      Fin.rev_eq_iff] <;> tauto

theorem RubikBand.sliceBand {n : ℕ} (a l : Fin n) (q : Rubik.Axis) (s : Rubik.Sticker n) :
  RubikBand.Band a (Rubik.sliceQuarter n q l s) ↔ RubikBand.Band a s := by
  by_cases h : Rubik.coordinate s.val.1 q = l
  · simpa only [Rubik.sliceQuarter, Equiv.coe_fn_mk, h, if_true] using
      RubikBand.rotationBand a q s
  · simp [Rubik.sliceQuarter, h]

theorem RubikBand.moveBand {n : ℕ} (a : Fin n) (m : Rubik.Move n) (s : Rubik.Sticker n) :
  RubikBand.Band a (Rubik.movePermutation m s) ↔ RubikBand.Band a s := by
  have hp : ∀ k : ℕ, ∀ t : Rubik.Sticker n,
      RubikBand.Band a (((Rubik.sliceQuarter n m.1 m.2.1)^k) t) ↔ RubikBand.Band a t := by
    intro k
    induction k with
    | zero => intro t; simp
    | succ k ih =>
      intro t
      simp only [pow_succ, Equiv.Perm.mul_apply]
      exact (ih _).trans (RubikBand.sliceBand a m.2.1 m.1 t)
  exact hp _ s

theorem RubikBand.deletionAgreesOutside {n : ℕ} (a : Fin n) (w : List (Rubik.Move n))
  (s : Rubik.Sticker n) (hs : ¬ RubikBand.Band a s) :
  RubikBand.wordPerm w s = RubikBand.wordPerm (RubikBand.faceDeletion a w) s := by
  induction w generalizing s with
  | nil => simp [RubikBand.wordPerm, RubikBand.faceDeletion]
  | cons m w ih =>
    by_cases hi : m.2.1 ≠ a ∧ m.2.1 ≠ a.rev
    · have ht := ih (Rubik.movePermutation m s) ((RubikBand.moveBand a m s).not.mpr hs)
      simpa [RubikBand.faceDeletion, RubikBand.wordPerm, List.reverse_cons,
        Equiv.Perm.mul_apply, hi] using ht
    · have hm : m.2.1 = a ∨ m.2.1 = a.rev := by tauto
      have hc : Rubik.coordinate s.val.1 m.1 ≠ m.2.1 := by
        intro he
        apply hs
        exact ⟨m.1, hm.imp (fun h => he.trans h) (fun h => he.trans h)⟩
      have hq : Rubik.sliceQuarter n m.1 m.2.1 s = s := by
        simp [Rubik.sliceQuarter, hc]
      have hp : ∀ k : ℕ, ((Rubik.sliceQuarter n m.1 m.2.1)^k) s = s := by
        intro k
        induction k with
        | zero => rfl
        | succ k ihk => simpa only [pow_succ, Equiv.Perm.mul_apply, hq] using ihk
      have hf : Rubik.movePermutation m s = s := hp _
      simpa [RubikBand.faceDeletion, RubikBand.wordPerm, List.reverse_cons,
        Equiv.Perm.mul_apply, hi, hf] using ih s hs

theorem RubikBand.strictOutside {n : ℕ} (a : Fin n) (w : List (Rubik.Move n))
  (hw : RubikBand.StrictControl a w) (s : Rubik.Sticker n)
  (hs : ¬ RubikBand.Band a s) : RubikBand.wordPerm w s = s := by
  calc
    RubikBand.wordPerm w s = RubikBand.wordPerm (RubikBand.faceDeletion a w) s :=
      RubikBand.deletionAgreesOutside a w s hs
    _ = s := by rw [hw.2]; rfl

open Rubik RubikWing
set_option linter.unusedSimpArgs false

 theorem RubikWing.pos_injective {n : ℕ} {c : Fin n} (hc : Admissible n c) :
    Function.Injective (pos c) := by
  have hlev := level_injective hc
  have he : Function.Injective (embedPos c) := by
    rintro ⟨x,y,z⟩ ⟨x',y',z'⟩ h
    have hx : x = x' := hlev (congrArg (fun p : Coord n => p.1) h)
    have hy : y = y' := hlev (congrArg (fun p : Coord n => p.2.1) h)
    have hz : z = z' := hlev (congrArg (fun p : Coord n => p.2.2) h)
    simp_all
  have href : Function.Injective (pos (1 : Fin 4)) := by decide
  have hpos (i : Label) : embedPos c (pos (1 : Fin 4) i) = pos c i := by
    fin_cases i <;> rfl
  intro i j hij
  apply href
  apply he
  rwa [hpos, hpos]

 theorem RubikWing.word_action {n : ℕ} {c : Fin n} (hc : Admissible n c)
    (w : Word) (i : Label) (b : Side) :
    physicalEval c w (lab c i b) = lab c (finiteEval w i) b := by
  have hword (w : Word) : ∀ i b,
      physicalEval c w (lab c i b) = lab c (finiteEval w i) b := by
    refine FreeGroup.induction_on w ?_ ?_ ?_ ?_
    · intro i b
      simp
    · intro t i b
      simpa [physicalEval, finiteEval] using physical_atom_lab hc t i b
    · intro t ht i b
      rw [map_inv, map_inv]
      apply Equiv.Perm.inv_eq_iff_eq.mpr
      simpa using (ht ((finiteEval (FreeGroup.of t))⁻¹ i) b).symm
    · intro u v hu hv i b
      rw [map_mul, map_mul, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hv, hu]
  exact hword w i b

namespace RubikWing
noncomputable section

def baseMove {n : ℕ} (c : Fin n) (a : Alphabet) : Move n := Sum.elim (faceMove c) (sliceMove c) a

def tokenMove {n : ℕ} (c : Fin n) (t : Token) : Move n :=
  let m := baseMove c t.1
  (m.1, m.2.1, if t.2 then 0 else 2)

def decode {n : ℕ} (c : Fin n) (ts : List Token) : List (Move n) := ts.reverse.map (tokenMove c)
def solverWord {n : ℕ} (c : Fin n) (σ : Equiv.Perm Label) : List (Move n) := decode c (solverTokens σ)
end
end RubikWing
