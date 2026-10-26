import RubikSTM.Definitions.OBTM.Periodic.SampleLaw
set_option autoImplicit false
noncomputable def RubikOBTM.Periodic.layerwiseUnion {T : ℕ} (hT : 0 < T) (K : Fin T → Type*) [∀ p, Group (K p)] (C : ∀ p, Finset (K p)) {k L R : ℕ} (books : Fin R → RubikOBTM.Periodic.Book hT K C k L) : RubikOBTM.Periodic.Book hT K C k L := by
  classical
  exact fun i => Finset.univ.biUnion (fun t => books t i)
