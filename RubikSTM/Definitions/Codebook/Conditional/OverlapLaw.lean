import RubikSTM.Definitions.FiniteProbability.ProductLaw
set_option autoImplicit false

namespace RubikCodebook.Conditional
open RubikJanson

noncomputable def overlapLaw {S U : Type*} [Fintype S] [Fintype U]
    (P : FiniteLaw S) (Q : FiniteLaw U) : FiniteLaw (S × U × U) where
  weight ω := P.weight ω.1 * Q.weight ω.2.1 * Q.weight ω.2.2
  nonneg ω := mul_nonneg (mul_nonneg (P.nonneg _) (Q.nonneg _)) (Q.nonneg _)
  total := by
    simp only [Fintype.sum_prod_type, ← Finset.mul_sum, Q.total, P.total, mul_one]

end RubikCodebook.Conditional

#print axioms RubikCodebook.Conditional.overlapLaw
#check RubikJanson.uniformLaw
