import Mathlib
import RubikSTM.Definitions.OBTM.Compiler.UniversalOwnProfile
import RubikSTM.Lemmas.OBTM.Compiler.PowModTwo
set_option autoImplicit false

theorem proof_RubikOBTMCompiler_odd_row_frame {G : Type*} [Group G] (Q F : G) (hQ : Q^2=1)
  (t j : ℕ) (hj : 1≤j) (hjt : j≤t) (ht : t%2=1) :
  Q^(t-j)*F*Q^(j-1) = (Q^((j-1)%2))⁻¹ * F * Q^((j-1)%2) := by
  have hsum : (t-j)+(j-1)=t-1 := by omega
  have hzero : (t-1)%2=0 := by omega
  have hp : Q^(t-1)=1 := by
    rw [RubikOBTMCompiler.pow_mod_two Q hQ,hzero,pow_zero]
  have hl : Q^(t-j)=(Q^((j-1)%2))⁻¹ := by
    calc
      Q^(t-j) = (Q^(t-j)*Q^(j-1))*(Q^(j-1))⁻¹ := by simp [mul_assoc]
      _ = (Q^(j-1))⁻¹ := by rw [← pow_add,hsum,hp,one_mul]
      _ = (Q^((j-1)%2))⁻¹ := by rw [RubikOBTMCompiler.pow_mod_two Q hQ]
  rw [hl,RubikOBTMCompiler.pow_mod_two Q hQ (j-1)]

#print axioms proof_RubikOBTMCompiler_odd_row_frame
