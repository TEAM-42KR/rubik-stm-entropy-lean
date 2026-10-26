import RubikSTM.Definitions.Orbits.SwapPhi
set_option autoImplicit false

theorem proof_RubikOrbit_flipLabel {n : ℕ} {a b : Fin n} (hg : RubikGeometry.Generic n a b)
  (hb : 0 < b.val ∧ b.val + 1 < n) (i : Fin 24) :
  RubikOrbit.minusLab a b hb i = RubikGeometry.lab b a (RubikOrbit.swapPhi i) := by
  have ha := hg.one_le_a
  have hb0 := hg.one_le_b
  have haS := hg.a_small
  have hbS := hg.b_small
  have hab : a.val ≠ b.val := by
    intro h
    exact hg.ne (Fin.ext h)
  have hiEq : RubikGeometry.hi b = RubikGeometry.hi a := rfl
  have loEq : RubikGeometry.lo b = RubikGeometry.lo a := rfl
  have hiRev : (RubikGeometry.hi a).rev = RubikGeometry.lo a := by
    apply Fin.ext
    change n - ((n-1)+1) = 0
    omega
  have loRev : (RubikGeometry.lo a).rev = RubikGeometry.hi a := by
    apply Fin.ext
    change n - (0+1) = n-1
    omega
  have hsep01 : (RubikGeometry.lo a : Fin n) ≠ RubikGeometry.hi a := by
    intro h
    have hh := congrArg Fin.val h
    change (0) = (n-1) at hh
    omega
  have hsep01r := Ne.symm hsep01
  have hsep02 : (RubikGeometry.lo a : Fin n) ≠ a := by
    intro h
    have hh := congrArg Fin.val h
    change (0) = (a.val) at hh
    omega
  have hsep02r := Ne.symm hsep02
  have hsep03 : (RubikGeometry.lo a : Fin n) ≠ a.rev := by
    intro h
    have hh := congrArg Fin.val h
    change (0) = (n-(a.val+1)) at hh
    omega
  have hsep03r := Ne.symm hsep03
  have hsep04 : (RubikGeometry.lo a : Fin n) ≠ b := by
    intro h
    have hh := congrArg Fin.val h
    change (0) = (b.val) at hh
    omega
  have hsep04r := Ne.symm hsep04
  have hsep05 : (RubikGeometry.lo a : Fin n) ≠ b.rev := by
    intro h
    have hh := congrArg Fin.val h
    change (0) = (n-(b.val+1)) at hh
    omega
  have hsep05r := Ne.symm hsep05
  have hsep12 : (RubikGeometry.hi a : Fin n) ≠ a := by
    intro h
    have hh := congrArg Fin.val h
    change (n-1) = (a.val) at hh
    omega
  have hsep12r := Ne.symm hsep12
  have hsep13 : (RubikGeometry.hi a : Fin n) ≠ a.rev := by
    intro h
    have hh := congrArg Fin.val h
    change (n-1) = (n-(a.val+1)) at hh
    omega
  have hsep13r := Ne.symm hsep13
  have hsep14 : (RubikGeometry.hi a : Fin n) ≠ b := by
    intro h
    have hh := congrArg Fin.val h
    change (n-1) = (b.val) at hh
    omega
  have hsep14r := Ne.symm hsep14
  have hsep15 : (RubikGeometry.hi a : Fin n) ≠ b.rev := by
    intro h
    have hh := congrArg Fin.val h
    change (n-1) = (n-(b.val+1)) at hh
    omega
  have hsep15r := Ne.symm hsep15
  have hsep23 : (a : Fin n) ≠ a.rev := by
    intro h
    have hh := congrArg Fin.val h
    change (a.val) = (n-(a.val+1)) at hh
    omega
  have hsep23r := Ne.symm hsep23
  have hsep24 : (a : Fin n) ≠ b := by
    intro h
    have hh := congrArg Fin.val h
    change (a.val) = (b.val) at hh
    omega
  have hsep24r := Ne.symm hsep24
  have hsep25 : (a : Fin n) ≠ b.rev := by
    intro h
    have hh := congrArg Fin.val h
    change (a.val) = (n-(b.val+1)) at hh
    omega
  have hsep25r := Ne.symm hsep25
  have hsep34 : (a.rev : Fin n) ≠ b := by
    intro h
    have hh := congrArg Fin.val h
    change (n-(a.val+1)) = (b.val) at hh
    omega
  have hsep34r := Ne.symm hsep34
  have hsep35 : (a.rev : Fin n) ≠ b.rev := by
    intro h
    have hh := congrArg Fin.val h
    change (n-(a.val+1)) = (n-(b.val+1)) at hh
    omega
  have hsep35r := Ne.symm hsep35
  have hsep45 : (b : Fin n) ≠ b.rev := by
    intro h
    have hh := congrArg Fin.val h
    change (b.val) = (n-(b.val+1)) at hh
    omega
  have hsep45r := Ne.symm hsep45
  fin_cases i <;> apply Subtype.ext <;>
    simp [RubikOrbit.minusLab, RubikIntertwiner.surfaceFlip,
      RubikIntertwiner.rawFlip, RubikIntertwiner.coordinateFlip, Equiv.swap_apply_def,
      RubikGeometry.lab, RubikGeometry.rawLab, RubikGeometry.posTable, RubikGeometry.normalTable,
      RubikOrbit.swapPhi, hiEq, loEq, hiRev, loRev, hsep01, hsep01r, hsep02, hsep02r, hsep03, hsep03r, hsep04, hsep04r, hsep05, hsep05r, hsep12, hsep12r, hsep13, hsep13r, hsep14, hsep14r, hsep15, hsep15r, hsep23, hsep23r, hsep24, hsep24r, hsep25, hsep25r, hsep34, hsep34r, hsep35, hsep35r, hsep45, hsep45r]

#print axioms proof_RubikOrbit_flipLabel
