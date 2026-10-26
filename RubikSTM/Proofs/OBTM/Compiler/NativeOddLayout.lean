import Mathlib
import RubikSTM.Definitions.OBTM.Compiler.NativeProgram
import RubikSTM.Lemmas.OBTM.Compiler.OddPadding
set_option autoImplicit false

theorem proof_RubikOBTMCompiler_native_odd_layout {n : ℕ} (X : Finset (Fin n)) {k : ℕ}
  (hk : 0 < k) : Nonempty (RubikOBTMCompiler.OddLayout X k) := by
  classical
  let q := RubikRectangle.rowCeil X.card k
  let t := q + RubikOBTMCompiler.oddPad q
  have hpad := RubikOBTMCompiler.odd_padding q
  have ht : 0 < t := by dsimp [t]; omega
  have hN : X.card ≤ q*k := by
    have hmod := Nat.mod_lt (X.card+k-1) hk
    have hdiv := Nat.div_add_mod (X.card+k-1) k
    rw [Nat.mul_comm] at hdiv
    change X.card ≤ ((X.card+k-1)/k)*k
    omega
  let rank := Fintype.equivFin X
  let pos (a : X) : Fin t × Fin k :=
    (⟨(rank a).val/k, by
       have hr : (rank a).val < X.card := by simpa using (rank a).isLt
       have hh : (rank a).val/k < q := (Nat.div_lt_iff_lt_mul hk).mpr (lt_of_lt_of_le hr hN)
       dsimp [t]; omega⟩,
      ⟨(rank a).val%k,Nat.mod_lt _ hk⟩)
  let f : Fin n → Fin t × Fin k :=
    Function.extend Subtype.val pos (fun _ => (⟨0,ht⟩,⟨0,hk⟩))
  have hf (a : X) : f a.val=pos a := Subtype.val_injective.extend_apply _ _ a
  refine ⟨⟨t,rfl,(fun a => (f a).1),(fun a => (f a).2),?_⟩⟩
  intro a ha b hb ho hr
  have hp : pos ⟨a,ha⟩=pos ⟨b,hb⟩ := by
    rw [← hf,← hf]
    exact Prod.ext ho hr
  have hq := congrArg (fun z : Fin t × Fin k => z.1.val) hp
  have hm := congrArg (fun z : Fin t × Fin k => z.2.val) hp
  have hval : (rank ⟨a,ha⟩).val=(rank ⟨b,hb⟩).val := by
    have h1 := Nat.div_add_mod (rank ⟨a,ha⟩).val k
    have h2 := Nat.div_add_mod (rank ⟨b,hb⟩).val k
    dsimp [pos] at hq hm
    rw [hq,hm] at h1
    omega
  exact congrArg Subtype.val (rank.injective (Fin.ext hval))

#print axioms proof_RubikOBTMCompiler_native_odd_layout
