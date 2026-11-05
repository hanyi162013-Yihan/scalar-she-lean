module
public import SHE.HalfAssignmentGain
public import SHE.AssignedSimplexIntegral

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
namespace SHE.AllocatedAssignmentKernel
open Set MeasureTheory Real GaussianAssignmentBlocks AssignmentGapPartition
  GapSimplexReflection GapSimplexFaces RootPowerGapKernels
open scoped BigOperators
open Classical
variable {k : ℕ}

def halfDensity (cs : List (Fin k×Fin (k+1))) (ν a fresh w : ℝ) (d : Fin k→ℝ) : ℝ :=
  if simplex w d then (slack w d)^(fresh-1)*(∏i,(d i)⁻¹)*sqrt (gain cs ν a d) else 0

theorem halfDensity_measurable (cs : List (Fin k×Fin (k+1))) (ν a fresh w : ℝ) :
    Measurable (halfDensity cs ν a fresh w) := by
  unfold halfDensity
  apply Measurable.ite (simplex_measurableSet w) _ measurable_const
  apply Measurable.mul
  · exact ((real_rpow_measurable _).comp (slack_measurable w)).mul
      (Finset.measurable_prod _ (fun i _=>(measurable_pi_apply i).inv))
  · apply Real.continuous_sqrt.measurable.comp
    unfold gain gainBlock
    apply Finset.measurable_prod
    intro l _
    split_ifs
    · apply Finset.measurable_prod
      intro j _
      exact measurable_const.min (measurable_const.mul ((real_rpow_measurable _).comp (measurable_pi_apply _)))
    · exact measurable_const
    · exact (real_rpow_measurable _).comp (MinimumGapChoice.choose_value_measurable
        (fun d : Fin k→ℝ=>d) (fun i=>measurable_pi_apply i) _ (by assumption))

/-- The repaired collision density is genuinely integrable. Rough
block gains are divided only among members of that same block. This
error-only estimate permits a fixed-cutoff frequency cost. -/
theorem halfDensity_integral_bound (cs : List (Fin k×Fin (k+1)))
    (hc : cs∈assignments (m:=k+1) (List.finRange k))
    {ν a fresh w : ℝ} (hν : 0≤ν) (ha : 0<a) (ha1 : a≤1)
    (hf : 0<fresh) (hf1 : fresh≤1) (hw : 0<w) :
    let p : Fin (k+1)→ℝ := Fin.cons fresh (fun i=>holderDegree cs hc a i/2)
    Integrable (halfDensity cs ν a fresh w) ∧
      (∫d,halfDensity cs ν a fresh w d)≤
        (max 1 ν)^((k:ℝ)/2)*(((k+1:ℕ):ℝ)^2/w*∏i,w^(p i)/(p i)) := by
  dsimp only
  let p : Fin (k+1)→ℝ := Fin.cons fresh (fun i=>holderDegree cs hc a i/2)
  have hp (i : Fin (k+1)) : 0<p i := Fin.cases hf (fun j=>
    div_pos (holderDegree_pos_le_one cs hc ha ha1 j).1 (by norm_num)) i
  have hp1 (i : Fin (k+1)) : p i≤1 := Fin.cases hf1 (fun j=>by
    change holderDegree cs hc a j/2≤1
    have h:holderDegree cs hc a j≤1 := (holderDegree_pos_le_one cs hc ha ha1 j).2
    linarith) i
  let C := (max 1 ν)^((k:ℝ)/2)
  have hC : 0≤C := Real.rpow_nonneg (zero_le_one.trans (le_max_left _ _)) _
  let G := GapSimplexFaces.density w (fun i=>kernel ν (p i) false)
  have hg := simplex_integral_bound hν hw p hp hp1 (fun _=>false)
  have hpoint (d : Fin k→ℝ) : halfDensity cs ν a fresh w d≤C*G d := by
    dsimp only [halfDensity,G,GapSimplexFaces.density]
    split_ifs with hd
    · have hb := mul_le_mul_of_nonneg_left (half_gain_bound cs hc hν ha.le d hd.1)
        (Real.rpow_nonneg hd.2.le (fresh-1))
      simpa only [p,kernel,Bool.false_eq_true,ite_false,Fin.cons_zero,Fin.cons_succ,C,mul_assoc,
        mul_left_comm,mul_comm] using hb
    · simp
  have hn (d : Fin k→ℝ) : 0≤halfDensity cs ν a fresh w d := by
    unfold halfDensity
    split_ifs with hd
    · exact mul_nonneg (mul_nonneg (Real.rpow_nonneg hd.2.le _)
        (Finset.prod_nonneg (fun i _=>inv_nonneg.mpr (hd.1 i).le))) (Real.sqrt_nonneg _)
    · exact le_rfl
  have hi : Integrable (halfDensity cs ν a fresh w) := (hg.1.const_mul C).mono'
    (halfDensity_measurable cs ν a fresh w).aestronglyMeasurable
      (ae_of_all _ (fun d=>by rw [Real.norm_of_nonneg (hn d)];exact hpoint d))
  refine ⟨hi,(integral_mono hi (hg.1.const_mul C) hpoint).trans ?_⟩
  rw [integral_const_mul]
  convert! mul_le_mul_of_nonneg_left hg.2 hC using 1

/-- The same repaired density on the literal newest-first old times,
using the actual Lebesgue-preserving gap map. -/
theorem ordered_halfDensity_integral_bound (cs : List (Fin k×Fin (k+1)))
    (hc : cs∈assignments (m:=k+1) (List.finRange k))
    {ν a fresh q T : ℝ} (hν : 0≤ν) (ha : 0<a) (ha1 : a≤1)
    (hf : 0<fresh) (hf1 : fresh≤1) (hqT : q<T) :
    let p : Fin (k+1)→ℝ := Fin.cons fresh (fun i=>holderDegree cs hc a i/2)
    Integrable (fun t : Fin k→ℝ=>if OrderedGapCoordinates.ordered q T k t then
      (slack (T-q) (OrderedGapCoordinates.gaps T k t))^(fresh-1)*
        (∏i,(OrderedGapCoordinates.gaps T k t i)⁻¹)*
          sqrt (gain cs ν a (OrderedGapCoordinates.gaps T k t)) else 0) ∧
      (∫t : Fin k→ℝ,if OrderedGapCoordinates.ordered q T k t then
        (slack (T-q) (OrderedGapCoordinates.gaps T k t))^(fresh-1)*
          (∏i,(OrderedGapCoordinates.gaps T k t i)⁻¹)*
            sqrt (gain cs ν a (OrderedGapCoordinates.gaps T k t)) else 0)≤
        (max 1 ν)^((k:ℝ)/2)*(((k+1:ℕ):ℝ)^2/(T-q)*∏i,(T-q)^(p i)/(p i)) := by
  dsimp only
  have hh := halfDensity_integral_bound cs hc hν ha ha1 hf hf1 (sub_pos.mpr hqT)
  have he : (fun d : Fin k→ℝ=>if (∀i,0<d i) ∧ (∑i,d i)<T-q then
      (slack (T-q) d)^(fresh-1)*(∏i,(d i)⁻¹)*sqrt (gain cs ν a d) else 0)=
      halfDensity cs ν a fresh (T-q) := by
    funext d
    simp only [halfDensity,simplex,slack,sub_pos]
  refine ⟨?_,?_⟩
  · have ht := (OrderedGapCoordinates.ordered_integrable_iff q T k
        (fun d=>(slack (T-q) d)^(fresh-1)*(∏i,(d i)⁻¹)*sqrt (gain cs ν a d))).mpr
          (by rw [he];exact hh.1)
    convert! ht using 1
  · have ht := OrderedGapCoordinates.ordered_integral q T k
        (fun d=>(slack (T-q) d)^(fresh-1)*(∏i,(d i)⁻¹)*sqrt (gain cs ν a d))
    rw [he] at ht
    exact (le_of_eq (by convert! ht using 1)).trans hh.2

end SHE.AllocatedAssignmentKernel
