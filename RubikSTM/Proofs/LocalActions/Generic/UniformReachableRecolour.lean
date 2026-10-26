import Mathlib
import RubikSTM.Definitions.OrbitGeometry.GenPerm
import RubikSTM.Definitions.LocalActions.Generic.ModelEval
import RubikSTM.Lemmas.LocalActions.Generic.UniformEvenRealization
import RubikSTM.Lemmas.OrbitGeometry.ExistsEvenRep
import RubikSTM.Lemmas.Orbits.ReachableColours
import RubikSTM.Lemmas.Construction.Control.Physical.ChronologicalApplyWord
import RubikSTM.Lemmas.OrbitGeometry.T.InverseOnLabels
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
open Rubik RubikGeometry
open RubikGeometry.T
open RubikLocal.Generic RubikConstruction.Control.Physical
theorem proof_RubikLocal_Generic_uniform_reachable_recolour : ∃ C : ℕ, ∀ (n : ℕ) (a b : Fin n),
    RubikGeometry.Generic n a b → ∀ c d : Colouring n, Reachable c → Reachable d →
      ∃ ms : List (Move n), ms.length ≤ C ∧
        (∀ i : Fin 24, applyWord ms c (RubikGeometry.lab a b i) = d (RubikGeometry.lab a b i)) ∧
        (∀ s : Sticker n, s ∉ Set.range (RubikGeometry.lab a b) → chronological ms s = s) ∧
        (∀ s : Sticker n, s ∉ Set.range (RubikGeometry.lab a b) → applyWord ms c s = c s) := by
  obtain ⟨C, hC⟩ := uniform_even_realization
  refine ⟨C, ?_⟩
  intro n a b hg c d hc hd
  obtain ⟨σc, hσc⟩ := RubikOrbit.reachable_colours hg c hc
  obtain ⟨σd, hσd⟩ := RubikOrbit.reachable_colours hg d hd
  obtain ⟨ec, hec, hce⟩ := RubikGeometry.exists_even_rep σc
  obtain ⟨ed, hed, hde⟩ := RubikGeometry.exists_even_rep σd
  have hcR (i : Fin 24) : c (RubikGeometry.lab a b i) = RubikGeometry.normalTable (ec i) :=
    congrFun (hσc.trans hce.symm) i
  have hdR (i : Fin 24) : d (RubikGeometry.lab a b i) = RubikGeometry.normalTable (ed i) :=
    congrFun (hσd.trans hde.symm) i
  let τ := ed⁻¹ * ec
  have hτ : τ ∈ alternatingGroup (Fin 24) :=
    (alternatingGroup (Fin 24)).mul_mem ((alternatingGroup (Fin 24)).inv_mem hed) hec
  obtain ⟨ms, hlen, hlocal⟩ := hC n a b hg τ hτ
  refine ⟨ms, hlen, ?_, hlocal.2, ?_⟩
  · intro i
    calc
      applyWord ms c (RubikGeometry.lab a b i) =
          c ((chronological ms)⁻¹ (RubikGeometry.lab a b i)) :=
        congrFun (chronological_applyWord ms c) _
      _ = c (RubikGeometry.lab a b (τ⁻¹ i)) :=
        congrArg c (RubikGeometry.T.inverse_on_labels _ _ _ hlocal.1 i)
      _ = RubikGeometry.normalTable (ec (τ⁻¹ i)) := hcR _
      _ = RubikGeometry.normalTable (ed i) := by simp [τ]
      _ = d (RubikGeometry.lab a b i) := (hdR i).symm
  · intro s hs
    have hinv : (chronological ms)⁻¹ s = s := by
      rw [Equiv.Perm.inv_eq_iff_eq, hlocal.2 s hs]
    simpa only [hinv] using congrFun (chronological_applyWord ms c) s
