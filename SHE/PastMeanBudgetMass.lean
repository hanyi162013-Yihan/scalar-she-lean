module

public import SHE.PastMeanBudgetClock

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SHE.PastMeanTimeFactors
open Set MeasureTheory Real PredictableL2 GaussianAssignmentBlocks PhysicalAssignmentGapScale
open AssignmentGapPartition AllocatedAssignmentKernel CoveredHistoryGeometry
open scoped ENNReal NNReal BigOperators
local instance pastMeanBudgetMass_finiteExponent : Fact ((2:ℝ≥0∞)≠⊤) := ⟨by simp⟩

/-- The ORIGINAL NNReal time-clock mass is bounded by the true
relative-span reflected budget, with no hidden horizon-normalization. -/
theorem currentBudget_mass_le (P : CanonicalCovariance.ProfileParameters) (ell : ℝ) (Cs : ℕ→ℝ)
    (k : ℕ) (ρ base T fresh A0 ν : ℝ) (hdegree : 0<ρ+2*fresh-1) (hT : base<T)
    (hν : 0≤ν) (H : ℝ≥0) :
    (∫ q,currentBudget P ell Cs k ρ base T fresh A0 ν q^2 ∂timeMeasure H)≤
      ∫ w,(w^(ρ/2)*QuarterRMSTimeFactors.oldTimeBudget P ell Cs k (T-base) ((T-base)-w) fresh A0 ν)^2
        ∂volume.restrict (Ioc 0 (T-base)) := by
  let f : ℝ→ℝ:=fun q=>(T-q)^(ρ/2)*QuarterRMSTimeFactors.oldTimeBudget P ell Cs k (T-base) (q-base) fresh A0 ν
  let g : ℝ→ℝ:=fun w=>w^(ρ/2)*QuarterRMSTimeFactors.oldTimeBudget P ell Cs k (T-base) ((T-base)-w) fresh A0 ν
  have hfm : Measurable f:=((measurable_const.sub measurable_id).pow_const _).mul
    ((QuarterRMSTimeFactors.oldTimeBudget_measurable P ell Cs k (T-base) fresh A0 ν).comp (measurable_id.sub_const base))
  have hgm : Measurable g:=(measurable_id.pow_const _).mul
    ((QuarterRMSTimeFactors.oldTimeBudget_measurable P ell Cs k (T-base) fresh A0 ν).comp (measurable_const.sub measurable_id))
  have hg:=(memLp_two_iff_integrable_sq_norm hgm.aestronglyMeasurable).mp
    (MeanRMSTimeFactors.fresh_budget_memLp P ell Cs k ρ (T-base) fresh A0 ν hdegree (sub_pos.mpr hT) hν)
  have hgi : IntervalIntegrable (fun w=>‖g w‖^2) volume 0 (T-base):=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (sub_nonneg.mpr hT.le)).mpr hg
  have hfi : IntervalIntegrable (fun q=>‖f q‖^2) volume base T:=by
    simpa only [f,g,sub_zero,show T-(T-base)=base by ring,
      show ∀ q : ℝ,(T-base)-(T-q)=q-base by intro q;ring] using (hgi.comp_sub_left T).symm
  have hfs : MemLp f 2 (volume.restrict (Ioc base T)):=
    (memLp_two_iff_integrable_sq_norm hfm.aestronglyMeasurable).mpr
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le hT.le).mp hfi)
  have hind : MemLp ((Ioc base T).indicator f) 2 volume:=
    (memLp_indicator_iff_restrict measurableSet_Ioc.nullMeasurableSet).mpr hfs
  let G : ℝ→ℝ:=fun q=>((Ioc base T).indicator f q)^2
  have hGm : Measurable G:=(hfm.indicator measurableSet_Ioc).pow_const 2
  have hGi : Integrable G volume:=by
    simpa only [G,Real.norm_eq_abs,sq_abs] using
      (memLp_two_iff_integrable_sq_norm (hfm.indicator measurableSet_Ioc).aestronglyMeasurable).mp hind
  have hclock : (∫ q,currentBudget P ell Cs k ρ base T fresh A0 ν q^2 ∂timeMeasure H)=
      ∫ q,G q ∂volume.restrict (Ioc 0 (H:ℝ)) := by
    rw [←timeMeasure_map H]
    exact (integral_map measurable_subtype_coe.aemeasurable hGm.aestronglyMeasurable).symm
  rw [hclock]
  apply (integral_mono_measure (Measure.restrict_le_self) (ae_of_all _ (fun q=>sq_nonneg _)) hGi).trans_eq
  have hG : G=(Ioc base T).indicator (fun q=>f q^2):=by
    funext q
    by_cases hq : q∈Ioc base T
    · simp only [G,indicator_of_mem hq]
    · simp only [G,indicator_of_notMem hq,zero_pow (by norm_num : (2:ℕ)≠0)]
  rw [hG,integral_indicator measurableSet_Ioc,
    ←intervalIntegral.integral_of_le hT.le,←intervalIntegral.integral_of_le (sub_nonneg.mpr hT.le)]
  have hs:=intervalIntegral.integral_comp_sub_left (fun w=>g w^2) T (a:=base) (b:=T)
  simpa only [f,g,sub_self,show ∀ q : ℝ,(T-base)-(T-q)=q-base by intro q;ring] using hs

/-- An explicit finite assignment bound for the actual current clock.
Every true root clip, rough count and empty-leaf relative-age gain is
retained. This is the mean constant needed after fixing the depth. -/
def assignmentMass (P : CanonicalCovariance.ProfileParameters) (ell : ℝ) (Cs : ℕ→ℝ)
    (k : ℕ) (ρ span fresh A0 ν : ℝ) : ℝ :=
  let cs:=assignments (m:=k+1) (List.finRange k)
  let v:=ν*sqrt (ProfileVariance.upperConstant*(P.lower/2))
  let degree:=fun i : Fin cs.length=>ρ+2*fresh-1+P.exponent*(roughCount (cs.get i):ℝ)/2
  (cs.length:ℝ)*∑ i : Fin cs.length,
    (MeanRMSTimeFactors.assignmentCoefficient P ell Cs k span fresh A0 i)^2*
    (span^(degree i)/(degree i)*rootMass v span^(2*rootCount (cs.get i)))

theorem currentBudget_assignment_bound (P : CanonicalCovariance.ProfileParameters) (ell : ℝ) (Cs : ℕ→ℝ)
    (k : ℕ) (ρ base T fresh A0 ν : ℝ) (hdegree : 0<ρ+2*fresh-1) (hT : base<T)
    (hν : 0≤ν) (H : ℝ≥0) :
    (∫ q,currentBudget P ell Cs k ρ base T fresh A0 ν q^2 ∂timeMeasure H)≤
      assignmentMass P ell Cs k ρ (T-base) fresh A0 ν := by
  exact (currentBudget_mass_le P ell Cs k ρ base T fresh A0 ν hdegree hT hν H).trans
    (MeanRMSTimeFactors.fresh_budget_square_bound P ell Cs k ρ (T-base) fresh A0 ν hdegree (sub_pos.mpr hT) hν)
end SHE.PastMeanTimeFactors
