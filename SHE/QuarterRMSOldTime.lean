module

public import SHE.QuarterRMSTimeFactors

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false

namespace SHE.QuarterRMSTimeFactors
open Set MeasureTheory Real StoppedFourier WordRecursion CutoffWordLevel CutoffWordHistories
  CutoffCarriers PhysicalScoreChain HistoryProductMeasure ActualMeanKernel ScalarMeanEnvelope
  QuarterSpatialEvent NormalizedKernelSplit RawTraceTimeEnvelope PhysicalAssignmentGapScale
  GaussianAssignmentBlocks AllocatedAssignmentKernel CoveredHistoryGeometry PhysicalParentGeometry
open scoped BigOperators
local instance quarterRMSOldTime_nativePositive : Fact (0<2*π) := ⟨by positivity⟩
variable {R : ReferenceData} (L : CutoffWordLevel.Level R HeatCircle 1)

/-- Explicit finite assignment budget, retaining each true rough/root
count, the full native age of empty leaves, and the retained root mass. -/
def oldTimeBudget (Q : CanonicalCovariance.ProfileParameters) (ell : ℝ) (Cs : ℕ→ℝ)
    (k : ℕ) (T q fresh A0 ν : ℝ) : ℝ :=
  let cs := assignments (m:=k+1) (List.finRange k)
  let v := ν*sqrt (ProfileVariance.upperConstant*(Q.lower/2))
  ∑ i : Fin cs.length,
    (scorePrefactor ell Cs k*prefactor Q (cs.get i) A0 1*T^((Q.exponent/4)*(emptyCount (cs.get i):ℝ)))*
      (((((k+1:ℕ):ℝ)^2/fresh)*inverseDegreeProduct (cs.get i) (List.get_mem cs i) (Q.exponent/4))*
        (T-q)^(fresh+(Q.exponent/4)*(roughCount (cs.get i):ℝ)-1)*rootMass v (T-q)^(rootCount (cs.get i)))

theorem total_old_time_budget (Q : CanonicalCovariance.ProfileParameters)
    (T : ℝ) (hT : ∀ p,L.terminal p=T) {ell : ℝ} (hell : 0<ell)
    (Cs : ℕ→ℝ) (hCs : ∀ j,0≤Cs j) (k : ℕ)
    {q fresh A0 ν : ℝ} (hqbase : R.base≤q) (hqT : q<T) (hTH : T≤R.horizon)
    (hf : 0<fresh) (hf1 : fresh≤1) (hA0 : 0≤A0) (hν : 0≤ν) :
    Integrable (fun t => totalIntegrand L Q ell Cs k q fresh A0 ν (anchor k t))
      (Measure.pi (fun _ : Fin k => volume.restrict (Ioc R.base R.horizon))) ∧
      (∫ t,totalIntegrand L Q ell Cs k q fresh A0 ν (anchor k t)
        ∂Measure.pi (fun _ : Fin k => volume.restrict (Ioc R.base R.horizon)))≤
          oldTimeBudget Q ell Cs k T q fresh A0 ν := by
  simpa only [anchor,oldTimeBudget] using actual_total_integral_bound L Q T hT hell Cs hCs k
    (0:HeatCircle) (fun _ => (0:HeatCircle)) hqbase hqT hTH hf hf1 hA0 hν

def rmsEnvelope (Q : CanonicalCovariance.ProfileParameters) (ell : ℝ) (Cs : ℕ→ℝ)
    (k : ℕ) (q A0 ν J ρ η cutoff Cf w U C lam tail E : ℝ) (t : Fin k→ℝ) : ℝ :=
  goodTimeFactor J ρ η cutoff k Cf ell w*sqrt E*
    totalIntegrand L Q ell Cs k q (freshDegree ρ η) A0 ν (anchor k t)+
      badTimeFactor U C k Cf ell lam tail*
        totalIntegrand L Q ell Cs k q (1/2:ℝ) A0 ν (anchor k t)

theorem totalIntegrand_nonneg (Q : CanonicalCovariance.ProfileParameters)
    {ell : ℝ} (hell : 0<ell) (Cs : ℕ→ℝ) (hCs : ∀ j,0≤Cs j)
    (k : ℕ) (q fresh A0 ν : ℝ) (p : History HeatCircle k) :
    0≤totalIntegrand L Q ell Cs k q fresh A0 ν p := by
  unfold totalIntegrand
  split_ifs with h
  · exact mul_nonneg (Real.rpow_nonneg (sub_pos.mpr h.2).le _)
      (mul_nonneg (timeWeight_nonneg L hell Cs hCs k p h.1)
        (SharpWordTimeScale.total_nonneg L Q k p q A0 ν))
  · exact le_rfl

theorem rmsEnvelope_nonneg (Q : CanonicalCovariance.ProfileParameters)
    {ell : ℝ} (hell : 0<ell) (Cs : ℕ→ℝ) (hCs : ∀ j,0≤Cs j)
    (k : ℕ) (q A0 ν J ρ η cutoff Cf w U C lam tail E : ℝ)
    (hcutoff : 0≤cutoff) (hw : 0≤w) (hlam : 0≤lam) (t : Fin k→ℝ) :
    0≤rmsEnvelope L Q ell Cs k q A0 ν J ρ η cutoff Cf w U C lam tail E t :=
  add_nonneg (mul_nonneg (mul_nonneg (goodTimeFactor_nonneg J ρ η hcutoff hw k Cf ell) (sqrt_nonneg _))
    (totalIntegrand_nonneg L Q hell Cs hCs k q _ A0 ν _))
      (mul_nonneg (badTimeFactor_nonneg U C hlam k Cf ell tail)
        (totalIntegrand_nonneg L Q hell Cs hCs k q _ A0 ν _))

/-- The actual good+bad RMS density is old-time L1 integrable before
the Itô square. Its exact finite assignment budget is derived, not an
assumed heat/time estimate. -/
theorem rms_old_time_budget (Q : CanonicalCovariance.ProfileParameters)
    (T : ℝ) (hT : ∀ p,L.terminal p=T) {ell : ℝ} (hell : 0<ell)
    (Cs : ℕ→ℝ) (hCs : ∀ j,0≤Cs j) (k : ℕ)
    {q A0 ν : ℝ} (hqbase : R.base≤q) (hqT : q<T) (hTH : T≤R.horizon)
    (hA0 : 0≤A0) (hν : 0≤ν) (J ρ η cutoff Cf w U C lam tail E : ℝ)
    (hρ : 0≤ρ) (hη : 0≤η) (hρη : ρ+η<1) (hcutoff : 0≤cutoff) (hw : 0≤w) (hlam : 0≤lam) :
    Integrable (rmsEnvelope L Q ell Cs k q A0 ν J ρ η cutoff Cf w U C lam tail E)
      (Measure.pi (fun _ : Fin k => volume.restrict (Ioc R.base R.horizon))) ∧
      (∫ t,rmsEnvelope L Q ell Cs k q A0 ν J ρ η cutoff Cf w U C lam tail E t
        ∂Measure.pi (fun _ : Fin k => volume.restrict (Ioc R.base R.horizon)))≤
        goodTimeFactor J ρ η cutoff k Cf ell w*sqrt E*
          oldTimeBudget Q ell Cs k T q (freshDegree ρ η) A0 ν+
            badTimeFactor U C k Cf ell lam tail*oldTimeBudget Q ell Cs k T q (1/2:ℝ) A0 ν := by
  have hg := total_old_time_budget L Q T hT hell Cs hCs k hqbase hqT hTH
    (freshDegree_pos hρη) (freshDegree_le_one hρ hη) hA0 hν
  have hb := total_old_time_budget L Q T hT hell Cs hCs k hqbase hqT hTH
    (by norm_num : (0:ℝ)<1/2) (by norm_num : (1/2:ℝ)≤1) hA0 hν
  refine ⟨(hg.1.const_mul _).add (hb.1.const_mul _),?_⟩
  change (∫ t,goodTimeFactor J ρ η cutoff k Cf ell w*sqrt E*
      totalIntegrand L Q ell Cs k q (freshDegree ρ η) A0 ν (anchor k t)+
      badTimeFactor U C k Cf ell lam tail*totalIntegrand L Q ell Cs k q (1/2:ℝ) A0 ν (anchor k t)
      ∂Measure.pi (fun _ : Fin k => volume.restrict (Ioc R.base R.horizon)))≤_
  rw [integral_add (hg.1.const_mul _) (hb.1.const_mul _),integral_const_mul,integral_const_mul]
  exact add_le_add
    (mul_le_mul_of_nonneg_left hg.2 (mul_nonneg (goodTimeFactor_nonneg J ρ η hcutoff hw k Cf ell) (sqrt_nonneg E)))
    (mul_le_mul_of_nonneg_left hb.2 (badTimeFactor_nonneg U C hlam k Cf ell tail))

end SHE.QuarterRMSTimeFactors
