import Mathlib
import RubikSTM.Definitions.OBTM.Compiler.UniversalOwnProfile
import RubikSTM.Lemmas.OBTM.Compiler.PowModTwo
import RubikSTM.Lemmas.WordConstruction.BaselineRestriction
set_option autoImplicit false

theorem proof_RubikOBTMCompiler_outside_restoration {G X : Type*} [Group G] [MulAction G X]
  (Q : G) (hQ : Q^2=1) (S : Set X) (hInv : ∀ x∈S, Q•x∈S)
  (phases : List (List G)) (hblocks : ∀ bs∈phases, ∀ f∈bs, ∀ x∈S, f•x=Q•x)
  (htotal : (phases.map List.length).sum%2=0) :
  ∀ x∈S, (phases.map (fun bs => bs.reverse.prod)).reverse.prod • x=x := by
  have hflat : (phases.map (fun bs => bs.reverse.prod)).reverse.prod = phases.flatten.reverse.prod := by
    clear hblocks htotal
    induction phases with
    | nil => simp
    | cons bs phases ih =>
      simpa only [List.map_cons,List.reverse_cons,List.prod_append,List.prod_singleton,
        List.flatten_cons,List.reverse_append] using congrArg (fun g : G => g*bs.reverse.prod) ih
  have hlen : phases.flatten.length=(phases.map List.length).sum := by
    induction phases with
    | nil => rfl
    | cons bs phases ih => simp [ih]
  have hb : ∀ f∈phases.flatten, ∀ x∈S, f•x=Q•x := by
    intro f hf
    obtain ⟨bs,hbs,hf⟩ := List.mem_flatten.mp hf
    exact hblocks bs hbs f hf
  intro x hx
  rw [hflat,RubikCompiler.baselineRestriction Q S hInv _ hb x hx,
    RubikOBTMCompiler.pow_mod_two Q hQ,hlen,htotal,pow_zero,one_smul]

#print axioms proof_RubikOBTMCompiler_outside_restoration
