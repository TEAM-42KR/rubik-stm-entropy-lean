import RubikSTM.Definitions.Wings.K
set_option autoImplicit false
open Rubik RubikWing
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false

 theorem RubikWing.control_equation (i : ControlIndex) :
    finiteOf (controlTokens i) = control i := by
  fin_cases i <;> decide

 theorem RubikWing.seed_equation : finiteOf seedTokens = seedPerm := by decide

 theorem RubikWing.control_deletion (i : ControlIndex) : deletion (freeControl i) = 1 := by
  fin_cases i <;> simp [freeControl, wordOf, controlTokens, tokenFree, deletion] <;> group

 theorem RubikWing.seed_deletion : deletion seedWord = 1 := by
  simp [seedWord, seedTokens, wordOf, tokenFree, deletion]

 theorem RubikWing.base_swap_equation : baseSwap = Equiv.swap (8 : Fin 24) 9 := by decide

 theorem RubikWing.adjacent_swap_equation (i : Fin 23) :
    pathPerm (adjacentPath i) * baseSwap * (pathPerm (adjacentPath i))⁻¹ =
      Equiv.swap i.castSucc i.succ := by
  fin_cases i <;> decide

 theorem RubikWing.strict_group_top : K = ⊤ := by
  have hcontrol (i : ControlIndex) : control i ∈ K :=
    Subgroup.subset_closure (Or.inl ⟨i, rfl⟩)
  have hseed : seedPerm ∈ K := Subgroup.subset_closure (Or.inr (Set.mem_singleton seedPerm))
  have hpath (w : List ControlIndex) : pathPerm w ∈ K := by
    induction w with
    | nil => exact K.one_mem
    | cons i w ih => exact K.mul_mem (hcontrol i) ih
  have hbase : baseSwap ∈ K := by
    exact K.mul_mem (hcontrol 0) (K.inv_mem (K.mul_mem
      (K.mul_mem (hpath triplePath) hseed) (K.inv_mem (hpath triplePath))))
  have hadj (i : Fin 23) : Equiv.swap i.castSucc i.succ ∈ K := by
    rw [← adjacent_swap_equation i]
    exact K.mul_mem (K.mul_mem (hpath _) hbase) (K.inv_mem (hpath _))
  have hgen : Submonoid.closure
      (Set.range fun i : Fin 23 => Equiv.swap i.castSucc i.succ) ≤ K.toSubmonoid := by
    rw [Submonoid.closure_le]
    rintro _ ⟨i, rfl⟩
    exact hadj i
  rw [Equiv.Perm.mclosure_swap_castSucc_succ 23] at hgen
  apply top_unique
  intro σ _
  exact hgen (by trivial)

 theorem RubikWing.strict_finite_realization (σ : Equiv.Perm Label) :
    ∃ w : Word, finiteEval w = σ ∧ deletion w = 1 := by
  have heval (w : List Token) : finiteEval (wordOf w) = finiteOf w := by
    induction w with
    | nil => simp [wordOf, finiteOf]
    | cons t w ih =>
      change finiteEval (tokenFree t * wordOf w) = tokenFinite t * finiteOf w
      rw [map_mul, ih]
      rcases t with ⟨a,b⟩
      cases b <;> simp [tokenFree, tokenFinite, finiteEval]
  have hg : ∀ g ∈ K, ∃ w : Word, finiteEval w = g ∧ deletion w = 1 := by
    intro g hg
    induction hg using Subgroup.closure_induction with
    | mem g hg =>
      rcases hg with h | h
      · obtain ⟨i, rfl⟩ := h
        exact ⟨freeControl i, (heval _).trans (control_equation i), control_deletion i⟩
      · have heq : g = seedPerm := Set.mem_singleton_iff.mp h
        subst g
        exact ⟨seedWord, (heval _).trans seed_equation, seed_deletion⟩
    | one => exact ⟨1, map_one _, map_one _⟩
    | mul g h _ _ ihg ihh =>
      obtain ⟨u, hu, hdu⟩ := ihg
      obtain ⟨v, hv, hdv⟩ := ihh
      refine ⟨u * v, ?_, ?_⟩
      · rw [map_mul, hu, hv]
      · rw [map_mul, hdu, hdv, one_mul]
    | inv g _ ih =>
      obtain ⟨u, hu, hdu⟩ := ih
      refine ⟨u⁻¹, ?_, ?_⟩
      · rw [map_inv, hu]
      · rw [map_inv, hdu, inv_one]
  exact hg σ (by rw [strict_group_top]; trivial)

namespace RubikWing
noncomputable section

def solver (σ : Equiv.Perm Label) : Word := Classical.choose (strict_finite_realization σ)

def solverTokens (σ : Equiv.Perm Label) : List Token := (solver σ).toWord

def uniformCost : ℕ := Finset.univ.sup (fun σ : Equiv.Perm Label => (solverTokens σ).length)
end
end RubikWing
