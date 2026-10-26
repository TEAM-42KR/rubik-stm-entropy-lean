import Mathlib
set_option autoImplicit false
open scoped Classical

theorem proof_RubikRectangle_partition_columns {n : ℕ} {T : Type*} (D : Finset T) (Y : Finset (Fin n))
    (choice : Fin n → T) (hchoice : ∀ b ∈ Y, choice b ∈ D) :
    (D.toList.flatMap (fun f => (Y.filter (fun b => choice b = f)).sort (· ≤ ·))).Perm
      (Y.sort (· ≤ ·)) := by
  classical
  have hnd : (D.toList.flatMap (fun f => (Y.filter (fun b => choice b = f)).sort (· ≤ ·))).Nodup := by
    apply List.nodup_flatMap.mpr
    refine ⟨fun f hf => Finset.sort_nodup _ _, ?_⟩
    apply List.Pairwise.imp _ D.nodup_toList
    intro f g hfg
    apply List.disjoint_left.mpr
    intro b hbf hbg
    have hf : b ∈ Y ∧ choice b = f := by simpa only [Finset.mem_sort, Finset.mem_filter] using hbf
    have hg : b ∈ Y ∧ choice b = g := by simpa only [Finset.mem_sort, Finset.mem_filter] using hbg
    exact hfg (hf.2.symm.trans hg.2)
  apply (List.perm_ext_iff_of_nodup hnd (Finset.sort_nodup _ _)).mpr
  intro b
  simp only [List.mem_flatMap, Finset.mem_toList, Finset.mem_sort, Finset.mem_filter]
  constructor
  · rintro ⟨f,hf,hb,he⟩
    exact hb
  · intro hb
    exact ⟨choice b,hchoice b hb,hb,rfl⟩

#print axioms proof_RubikRectangle_partition_columns
