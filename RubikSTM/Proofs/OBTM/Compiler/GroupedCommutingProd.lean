import Mathlib
set_option autoImplicit false
open scoped IsMulCommutative

theorem proof_RubikOBTMCompiler_grouped_commuting_prod {I P G : Type*} [DecidableEq P] [Monoid G]
  (Y : Finset I) (v : I → G) (hc : ∀ i j, Commute (v i) (v j))
  (w : I → P) (A : Finset P) (hw : ∀ d∈Y, w d∈A) :
  (A.toList.map (fun p => (((Y.filter (fun d => w d=p)).toList).map v).reverse.prod)).reverse.prod =
    (Y.toList.map v).reverse.prod := by
  classical
  let H := Submonoid.closure (Set.range v)
  letI : IsMulCommutative H := Submonoid.isMulCommutative_closure G (by
    rintro _ ⟨i,rfl⟩ _ ⟨j,rfl⟩
    exact (hc i j).eq)
  let V : I → H := fun i => ⟨v i,Submonoid.subset_closure ⟨i,rfl⟩⟩
  have ht (S : Finset I) : ((S.toList.map V).reverse.prod) = ∏ i∈S, V i := by
    rw [List.prod_reverse]
    simpa only [Finset.toList_toFinset] using (List.prod_toFinset V S.nodup_toList).symm
  have he : (A.toList.map (fun p => (((Y.filter (fun d => w d=p)).toList).map V).reverse.prod)).reverse.prod =
      (Y.toList.map V).reverse.prod := by
    rw [List.prod_reverse]
    simp only [ht]
    rw [← List.prod_toFinset _ A.nodup_toList,Finset.toList_toFinset]
    exact Finset.prod_fiberwise_of_maps_to (s:=Y) (t:=A) (g:=w) hw V
  have hh := congrArg H.subtype he
  simp only [map_list_prod,List.map_reverse,List.map_map,Function.comp_def] at hh
  change (A.toList.map (fun p => (((Y.filter (fun d => w d=p)).toList).map v).reverse.prod)).reverse.prod =
    (Y.toList.map v).reverse.prod at hh
  exact hh

#print axioms proof_RubikOBTMCompiler_grouped_commuting_prod
