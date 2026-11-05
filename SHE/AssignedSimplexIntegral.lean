module

public import SHE.AssignmentGapDegrees

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
noncomputable section

namespace SHE.AllocatedAssignmentKernel
open Set MeasureTheory Real GaussianAssignmentBlocks AssignmentGapPartition RootPowerGapKernels
  GapSimplexReflection GapSimplexFaces
open scoped BigOperators
open Classical
variable {k m : ℕ}

def assignedDensity (cs : List (Fin k×Fin (m+1))) (ν a fresh w : ℝ) (d : Fin k→ℝ) : ℝ :=
  if simplex w d then (slack w d)^(fresh-1)*weight cs ν a d else 0

theorem weight_measurable (cs : List (Fin k×Fin (m+1))) (ν a : ℝ) : Measurable (weight cs ν a) := by
  apply Finset.measurable_prod
  intro l _
  unfold blockWeight
  split_ifs with hl hb
  · exact Finset.measurable_prod _ (fun j _=>(rootKernel_measurable ν).comp (measurable_pi_apply _))
  · exact measurable_const
  · have hp := Finset.measurable_prod (Finset.univ : Finset (Fin (block cs l).length))
      (fun j _=>(measurable_pi_apply ((block cs l).get j) :
        Measurable (fun d : Fin k→ℝ=>d ((block cs l).get j))).inv)
    convert! hp.mul ((real_rpow_measurable a).comp (MinimumGapChoice.choose_value_measurable
        (fun d : Fin k→ℝ=>d) (fun i=>measurable_pi_apply i) (block cs l) hb)) using 1

theorem assignedDensity_measurable (cs : List (Fin k×Fin (m+1))) (ν a fresh w : ℝ) :
    Measurable (assignedDensity cs ν a fresh w) :=
  Measurable.ite (simplex_measurableSet w)
    (((real_rpow_measurable _).comp (slack_measurable w)).mul (weight_measurable cs ν a)) measurable_const

theorem assignedDensity_nonneg (cs : List (Fin k×Fin (m+1))) {ν : ℝ} (hν : 0≤ν)
    (a fresh w : ℝ) (d : Fin k→ℝ) : 0≤assignedDensity cs ν a fresh w d := by
  unfold assignedDensity
  split_ifs with h
  · exact mul_nonneg (Real.rpow_nonneg h.2.le _) (Finset.prod_nonneg
      (fun l _=>blockWeight_nonneg cs hν d h.1 l))
  · exact le_rfl

/-- The real ordered-time integral of every actual finite assignment
has its full rough-block degree and exact clipped root mass. -/
theorem assignedDensity_integral_bound (cs : List (Fin k×Fin (m+1)))
    (hc : cs∈assignments (m:=m+1) (List.finRange k))
    {ν a fresh w : ℝ} (hν : 0≤ν) (ha : 0<a) (ha1 : a≤1)
    (hf : 0<fresh) (hf1 : fresh≤1) (hw : 0<w) :
    Integrable (assignedDensity cs ν a fresh w) ∧
      (∫ d,assignedDensity cs ν a fresh w d)≤
        (((k+1:ℕ):ℝ)^2/fresh*inverseDegreeProduct cs hc a)*
          w^(fresh+a*(roughCount cs:ℝ)-1)*rootMass ν w^(rootCount cs) := by
  let p : Fin (k+1)→ℝ := Fin.cons fresh (degree cs hc a)
  let r : Fin (k+1)→Bool := Fin.cons false (rootFlag cs hc)
  have hp (i : Fin (k+1)) : 0<p i := Fin.cases hf (fun j=>(degree_pos_le_one cs hc ha ha1 j).1) i
  have hp1 (i : Fin (k+1)) : p i≤1 := Fin.cases hf1 (fun j=>(degree_pos_le_one cs hc ha ha1 j).2) i
  have hh := RootPowerGapKernels.simplex_integral_bound hν hw p hp hp1 r
  have hdom (d : Fin k→ℝ) : assignedDensity cs ν a fresh w d≤
      GapSimplexFaces.density w (fun i=>kernel ν (p i) (r i)) d := by
    unfold assignedDensity GapSimplexFaces.density
    split_ifs with hd
    · simp only [p,r,Fin.cons_zero,Fin.cons_succ,kernel,Bool.false_eq_true,ite_false]
      exact mul_le_mul_of_nonneg_left (weight_le_allocated cs hc hν ha.le d hd.1)
        (Real.rpow_nonneg hd.2.le _)
    · exact le_rfl
  have hin : Integrable (assignedDensity cs ν a fresh w) :=
    hh.1.mono' (assignedDensity_measurable cs ν a fresh w).aestronglyMeasurable
      (ae_of_all _ (fun d=>by rw [Real.norm_of_nonneg (assignedDensity_nonneg cs hν a fresh w d)];exact hdom d))
  refine ⟨hin,(integral_mono hin hh.1 hdom).trans (hh.2.trans_eq ?_)⟩
  have hm : (∏ i,mass ν (p i) (r i) w)=
      (w^fresh/fresh)*inverseDegreeProduct cs hc a*
        w^(a*(roughCount cs:ℝ))*rootMass ν w^(rootCount cs) := by
    rw [Fin.prod_univ_succ]
    simp only [p,r,Fin.cons_zero,Fin.cons_succ]
    rw [prod_mass hw,root_count_eq,total_degree]
    dsimp only [mass,inverseDegreeProduct]
    simp only [Bool.false_eq_true,ite_false]
    ring
  rw [hm]
  have he : w⁻¹*(w^fresh*w^(a*(roughCount cs:ℝ)))=w^(fresh+a*(roughCount cs:ℝ)-1) := by
    rw [←Real.rpow_neg_one,←Real.rpow_add hw,←Real.rpow_add hw]
    congr 1
    ring
  calc
    _ = (((k+1:ℕ):ℝ)^2/fresh*inverseDegreeProduct cs hc a)*
        (w⁻¹*(w^fresh*w^(a*(roughCount cs:ℝ))))*rootMass ν w^(rootCount cs) := by ring
    _ = _ := by rw [he]

/-- The same bound on the literal newest-first ordered time variables,
using the proved Lebesgue-preserving map rather than a formal simplex. -/
theorem ordered_assignment_integral_bound (cs : List (Fin k×Fin (m+1)))
    (hc : cs∈assignments (m:=m+1) (List.finRange k))
    {ν a fresh q T : ℝ} (hν : 0≤ν) (ha : 0<a) (ha1 : a≤1)
    (hf : 0<fresh) (hf1 : fresh≤1) (hqT : q<T) :
    Integrable (fun t : Fin k→ℝ=>if OrderedGapCoordinates.ordered q T k t then
      (GapSimplexReflection.slack (T-q) (OrderedGapCoordinates.gaps T k t))^(fresh-1)*
        weight cs ν a (OrderedGapCoordinates.gaps T k t) else 0) ∧
      (∫ t : Fin k→ℝ,if OrderedGapCoordinates.ordered q T k t then
        (GapSimplexReflection.slack (T-q) (OrderedGapCoordinates.gaps T k t))^(fresh-1)*
          weight cs ν a (OrderedGapCoordinates.gaps T k t) else 0)≤
        (((k+1:ℕ):ℝ)^2/fresh*inverseDegreeProduct cs hc a)*
          (T-q)^(fresh+a*(roughCount cs:ℝ)-1)*rootMass ν (T-q)^(rootCount cs) := by
  have hh := assignedDensity_integral_bound cs hc hν ha ha1 hf hf1 (sub_pos.mpr hqT)
  have he : (fun d : Fin k→ℝ=>if (∀ i,0<d i) ∧ (∑ i,d i)<T-q then
      (slack (T-q) d)^(fresh-1)*weight cs ν a d else 0)=assignedDensity cs ν a fresh (T-q) := by
    funext d
    simp only [assignedDensity,simplex,slack,sub_pos]
  refine ⟨?_,?_⟩
  · have ht := (OrderedGapCoordinates.ordered_integrable_iff q T k
        (fun d=>(slack (T-q) d)^(fresh-1)*weight cs ν a d)).mpr (by rw [he];exact hh.1)
    convert! ht using 1
  · have ht := OrderedGapCoordinates.ordered_integral q T k
        (fun d=>(slack (T-q) d)^(fresh-1)*weight cs ν a d)
    rw [he] at ht
    calc
      _ = ∫ d,assignedDensity cs ν a fresh (T-q) d := by convert! ht using 1
      _ ≤ _ := hh.2

end SHE.AllocatedAssignmentKernel
