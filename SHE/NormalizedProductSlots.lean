module

public import SHE.NormalizedProductTelescope

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
namespace SHE.NormalizedProductTelescope
open scoped BigOperators
open Classical
variable {m:ℕ}

/-- The exact ordered telescope term is a product with precisely one
normalized paired factor, old factors before it and new factors after it. -/
theorem term_eq_product (new old source:Fin m→ℝ) (i:Fin m) :
    term new old source i=∏j:Fin m,
      if j=i then NormalizedScalarMoment.value (new i-old i) (source i)
      else if i<j then new j else old j := by
  let f:Fin m→ℝ:=fun j=>if j=i then NormalizedScalarMoment.value (new i-old i) (source i)
    else if i<j then new j else old j
  have he:(Finset.univ:Finset (Fin m)).erase i=
      (Finset.univ.filter (fun j:Fin m=>j < i))∪(Finset.univ.filter (fun j:Fin m=>i < j)) := by
    ext j
    simp only [Finset.mem_erase,Finset.mem_univ,and_true,Finset.mem_union,Finset.mem_filter,true_and]
    exact ne_iff_lt_or_gt
  have hd:Disjoint (Finset.univ.filter (fun j:Fin m=>j < i))
      (Finset.univ.filter (fun j:Fin m=>i < j)) := by
    apply Finset.disjoint_left.mpr
    intro j hj hj'
    exact (not_lt_of_ge (Finset.mem_filter.mp hj).2.le) (Finset.mem_filter.mp hj').2
  rw [←Finset.mul_prod_erase Finset.univ f (Finset.mem_univ i),he,Finset.prod_union hd]
  have hleft:(∏j ∈ Finset.univ.filter (fun j:Fin m=>j < i),f j)=
      ∏j ∈ Finset.univ.filter (fun j:Fin m=>j < i),old j := by
    apply Finset.prod_congr rfl
    intro j hj
    have hj' : j < i :=(Finset.mem_filter.mp hj).2
    simp only [f,ne_of_lt hj',ite_false,not_lt_of_ge hj'.le]
  have hright:(∏j ∈ Finset.univ.filter (fun j:Fin m=>i < j),f j)=
      ∏j ∈ Finset.univ.filter (fun j:Fin m=>i < j),new j := by
    apply Finset.prod_congr rfl
    intro j hj
    have hj' : i < j :=(Finset.mem_filter.mp hj).2
    simp only [f,(ne_of_lt hj').symm,ite_false,hj',ite_true]
  rw [hleft,hright]
  simp only [f,ite_true,term]
  ring

end SHE.NormalizedProductTelescope
