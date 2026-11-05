module

public import SHE.PairedPhysicalGapScale
public import SHE.PairedRemainderTime

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2100000
noncomputable section
namespace SHE.PairedPhysicalGapScale
open Set MeasureTheory Real GaussianAssignmentBlocks HeterogeneousAssignmentKernel
open scoped BigOperators
open Classical
variable {k:ℕ}

theorem prefactor_nonneg (P:CanonicalCovariance.ProfileParameters) (cs:List (Fin k×Fin (k+1)))
    (j0:Fin k) (χ:ℝ) {A0:ℝ} (hA0:0≤A0):0≤prefactor P cs j0 χ A0 := by
  have hH:=P.holder_nonneg
  have hl:=P.lower_pos
  have hu:=ProfileVariance.upperConstant_pos
  unfold prefactor
  apply mul_nonneg (by positivity)
  apply Finset.prod_nonneg
  intro j _
  unfold leafPrefactor PhysicalAssignmentGapScale.leafPrefactor
  split_ifs <;> positivity

/-- The actual old inverse gaps times every physical rough/root scale
are genuinely integrable, including arbitrary original full ages varying
with the simplex point. All N rough gains survive; only the paired slot
costs chi/4, and every original old root clip remains in rootMass. -/
theorem physical_scale_integral (P:CanonicalCovariance.ProfileParameters)
    (cs:List (Fin k×Fin (k+1))) (hc:cs∈assignments (m:=k+1) (List.finRange k))
    (j0:Fin k) {χ w A0 ν:ℝ} (hχ:0≤χ) (hχβ:χ<P.exponent) (hw:0<w)
    (hA0:0≤A0) (hν:0≤ν) (age:(Fin k→ℝ)→Fin k→ℝ)
    (hmeas:∀j,Measurable (fun d=>age d j))
    (hage:∀d,GapSimplexFaces.simplex w d→∀j,0≤age d j ∧ age d j≤w):
    let F:=fun d:Fin k→ℝ=>if GapSimplexFaces.simplex w d then
      (∏j,(d j)⁻¹)*factor P cs j0 χ d (age d) A0 ν else 0
    Integrable F ∧ (∫d,F d)≤prefactor P cs j0 χ A0*
      (((k+1:ℕ):ℝ)^2*inverseDegreeProduct cs hc (pairedDegree P.exponent χ j0))*
        w^((k:ℝ)*P.exponent/4-χ/4)*
          rootMass (ν*sqrt (ProfileVariance.upperConstant*(P.lower/2))) w^
            (AllocatedAssignmentKernel.rootCount cs) := by
  intro F
  let a:=pairedDegree P.exponent χ j0
  let freq:=ν*sqrt (ProfileVariance.upperConstant*(P.lower/2))
  let C:=prefactor P cs j0 χ A0
  have hC:0≤C:=prefactor_nonneg P cs j0 χ hA0
  have hf:0≤freq:=mul_nonneg hν (sqrt_nonneg _)
  have ha:∀j:Fin k,0≤a j.succ:=fun j=>
    (pairedDegree_pos_le_one P.exponent_pos P.exponent_le_one hχ hχβ j0 j.succ).1.le
  have hh:=PairedRemainderTime.paired_density_integral_bound cs hc hf P.exponent_pos
    P.exponent_le_one hχ hχβ hw j0
  let G:=fun d:Fin k→ℝ=>w^(emptyDegree cs a)*assignedDensity cs freq a 1 w d
  have hG:Integrable G:=hh.1
  have hem:Measurable (fun d:Fin k→ℝ=>emptyGain cs a (age d)):=by
    unfold emptyGain
    apply Finset.measurable_prod
    intro j _
    split_ifs
    · exact (hmeas j).pow_const _
    · exact measurable_const
  have hm:Measurable F := by
    have he:F=(fun d:Fin k→ℝ=>if GapSimplexFaces.simplex w d then
        C*weight cs freq a d*emptyGain cs a (age d) else 0):=by
      funext d
      by_cases hd:GapSimplexFaces.simplex w d
      · simp only [F,hd,ite_true]
        exact inverse_factor_eq P cs hc j0 χ d (age d) (fun j=>(hage d hd j).1) A0 ν
      · simp only [F,hd,ite_false]
    rw [he]
    exact Measurable.ite (GapSimplexFaces.simplex_measurableSet w)
      ((measurable_const.mul (weight_measurable cs freq a)).mul hem) measurable_const
  have hb(d:Fin k→ℝ):0≤F d ∧ F d≤C*G d := by
    by_cases hd:GapSimplexFaces.simplex w d
    · have hk:0≤weight cs freq a d:=Finset.prod_nonneg (fun l _=>blockWeight_nonneg cs hf d hd.1 l)
      have he0:0≤emptyGain cs a (age d):=by
        unfold emptyGain
        apply Finset.prod_nonneg
        intro j _
        split_ifs <;> first |exact rpow_nonneg (hage d hd j).1 _|exact zero_le_one
      have he:=emptyGain_bound cs a ha hw (age d) (hage d hd)
      simp only [F,hd,ite_true]
      rw [inverse_factor_eq P cs hc j0 χ d (age d) (fun j=>(hage d hd j).1) A0 ν]
      refine ⟨mul_nonneg (mul_nonneg hC hk) he0,?_⟩
      have ht:=mul_le_mul_of_nonneg_left he (mul_nonneg hC hk)
      convert! ht using 1
      simp only [G,assignedDensity,hd,ite_true,sub_self,Real.rpow_zero,mul_one,one_mul]
      ring
    · simp only [F,G,assignedDensity,hd,ite_false,mul_zero,le_refl,and_self]
  have hi:Integrable F:=(hG.const_mul C).mono' hm.aestronglyMeasurable
    (ae_of_all _ (fun d=>by rw [Real.norm_of_nonneg (hb d).1];exact (hb d).2))
  refine ⟨hi,?_⟩
  have ht:(∫d,F d)≤C*
      (((k+1:ℕ):ℝ)^2*inverseDegreeProduct cs hc a)*w^((k:ℝ)*P.exponent/4-χ/4)*
        rootMass freq w^(AllocatedAssignmentKernel.rootCount cs) := by
    apply (integral_mono hi (hG.const_mul C) (fun d=>(hb d).2)).trans
    rw [integral_const_mul]
    convert! mul_le_mul_of_nonneg_left hh.2 hC using 1 <;> ring
  exact ht

end SHE.PairedPhysicalGapScale
