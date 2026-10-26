import RubikSTM.Definitions.OBTM.Finite.Act
import RubikSTM.Definitions.Channel.Transition
import RubikSTM.Definitions.FiniteProbability.ProductLaw
set_option autoImplicit false

namespace RubikOBTM.Finite
open scoped Classical

abbrev Intrinsic := Toggle × Toggle

noncomputable def nativeC : Finset Intrinsic :=
  Finset.univ.filter (fun v => v.1 ≠ 1 ∧ v.2 ≠ 1)

def nativeWitness : Native :=
  (⟨Multiplicative.ofAdd (1,0),by decide⟩,⟨Multiplicative.ofAdd (0,1),by decide⟩)
instance : Nonempty Native := ⟨nativeWitness⟩

def phaseHom (i : Phase) : Intrinsic →* G := (embed i).prodMap (embed i)
def phaseAct (i : Phase) : Intrinsic →* Equiv.Perm Z := act.comp (phaseHom i)

noncomputable def nativeEquiv : Native ≃ {v : Intrinsic // v ∈ nativeC} where
  toFun c := ⟨(c.1.val,c.2.val),by simpa [nativeC] using And.intro c.1.property c.2.property⟩
  invFun v := by
    have h : v.val.1 ≠ 1 ∧ v.val.2 ≠ 1 := by simpa [nativeC] using v.property
    exact (⟨v.val.1,h.1⟩,⟨v.val.2,h.2⟩)
  left_inv _ := rfl
  right_inv _ := rfl

def subgroupLetter (i : Phase) (c : Native) : K i :=
  ⟨letter i c,⟨⟨c.1.val,rfl⟩,⟨c.2.val,rfl⟩⟩⟩

noncomputable def regular (i : Phase) : Matrix (K i) (K i) ℝ :=
  RubikChannel.transition (RubikJanson.uniformLaw (inferInstance : Nonempty Native))
    (fun c => Equiv.mulLeft (subgroupLetter i c))

noncomputable def periodicC (i : Fin period) : Finset Intrinsic := nativeC
noncomputable def periodicAct (i : Fin period) : Intrinsic →* Equiv.Perm Z := phaseAct (phaseAt i)

end RubikOBTM.Finite
