module

public import SHE.QuarterBudgetClock
public import SHE.MeanRMSTimeFactors

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false

namespace SHE.MeanRMSTimeFactors
open Set MeasureTheory Real PhysicalAssignmentGapScale GaussianAssignmentBlocks AssignmentGapPartition
  AllocatedAssignmentKernel CoveredHistoryGeometry QuarterRMSTimeFactors PredictableL2
open scoped ENNReal NNReal BigOperators
local instance meanBudgetSquare_finiteExponent : Fact ((2:ℝ≥0∞)≠⊤) := ⟨by simp⟩

def squareKernel (ρ β ν : ℝ) (a b : ℕ) (w : ℝ) : ℝ :=
  w^(ρ/2+β*(b:ℝ)/4-1/2)*rootMass ν w^a

/-- The actual negative-output gain makes the current-time endpoint
square integrable even at depth zero. Root clipping is retained, with
only its finite-interval bound used for this integrability result. -/
theorem squareKernel_memLp {ρ β ν T : ℝ} (hρ : 0<ρ) (hβ : 0≤β)
    (hν : 0≤ν) (hT : 0<T) (a b : ℕ) :
    MemLp (squareKernel ρ β ν a b) 2 (volume.restrict (Ioc 0 T)) := by
  have hd : -1<ρ+β*(b:ℝ)/2-1 := by
    have hb : 0≤β*(b:ℝ)/2 := by positivity
    linarith
  have hi : Integrable (fun w : ℝ => w^(ρ+β*(b:ℝ)/2-1))
      (volume.restrict (Ioc 0 T)) :=
    (intervalIntegral.intervalIntegrable_rpow' hd).1
  have hm : Measurable (squareKernel ρ β ν a b) :=
    (real_rpow_measurable _).mul ((rootMass_measurable ν).pow_const a)
  apply (memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).mpr
  apply (hi.const_mul (rootMass ν T^(2*a))).mono' ((hm.norm).pow_const 2).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with w hw
  have hr : 0≤rootMass ν w := rootMass_nonneg hν hw.1.le
  have he : ‖squareKernel ρ β ν a b w‖^2=
      w^(ρ+β*(b:ℝ)/2-1)*rootMass ν w^(2*a) := by
    unfold squareKernel
    rw [Real.norm_of_nonneg (mul_nonneg (Real.rpow_nonneg hw.1.le _) (pow_nonneg hr _))]
    rw [mul_pow,←Real.rpow_mul_natCast hw.1.le,←pow_mul,Nat.mul_comm a 2]
    congr 2
    ring
  rw [he]
  rw [Real.norm_of_nonneg (mul_nonneg (Real.rpow_nonneg hw.1.le _) (pow_nonneg hr _)),mul_comm (rootMass ν T^(2*a))]
  exact mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ hr (rootMass_mono hν hw.1.le hw.2) _) (Real.rpow_nonneg hw.1.le _)

/-- The literal finite assignment budget, including its zero-depth
term, has a genuine current-time L2 kernel after the output gain. -/
theorem budget_memLp (Q : CanonicalCovariance.ProfileParameters) (ell : ℝ) (Cs : ℕ→ℝ)
    (k : ℕ) (ρ T A0 ν : ℝ) (hρ : 0<ρ) (hT : 0<T) (hν : 0≤ν) :
    MemLp (fun w => w^(ρ/2)*oldTimeBudget Q ell Cs k T (T-w) (1/2:ℝ) A0 ν) 2
      (volume.restrict (Ioc 0 T)) := by
  let cs := assignments (m:=k+1) (List.finRange k)
  let v := ν*sqrt (ProfileVariance.upperConstant*(Q.lower/2))
  let K := fun i : Fin cs.length =>
    (scorePrefactor ell Cs k*PhysicalAssignmentGapScale.prefactor Q (cs.get i) A0 1*T^((Q.exponent/4)*(emptyCount (cs.get i):ℝ)))*
      (((k+1:ℕ):ℝ)^2/(1/2:ℝ)*inverseDegreeProduct (cs.get i) (List.get_mem cs i) (Q.exponent/4))
  have hv : 0≤v := mul_nonneg hν (sqrt_nonneg _)
  have hp (i : Fin cs.length) : MemLp
      (fun w => K i*squareKernel ρ Q.exponent v (rootCount (cs.get i)) (roughCount (cs.get i)) w)
      2 (volume.restrict (Ioc 0 T)) :=
    (squareKernel_memLp hρ Q.exponent_pos.le hv hT _ _).const_mul _
  have hs := memLp_finsetSum Finset.univ (fun i _ => hp i)
  apply hs.ae_eq
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with w hw
  rw [oldTimeBudget,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp only [show T-(T-w)=w by ring]
  dsimp only [K,squareKernel,v,cs]
  rw [show (1/2:ℝ)+(Q.exponent/4)*(roughCount ((assignments (List.finRange k)).get i):ℝ)-1=
    Q.exponent*(roughCount ((assignments (List.finRange k)).get i):ℝ)/4-1/2 by ring]
  rw [show ρ/2+Q.exponent*(roughCount ((assignments (List.finRange k)).get i):ℝ)/4-1/2=
    ρ/2+(Q.exponent*(roughCount ((assignments (List.finRange k)).get i):ℝ)/4-1/2) by ring,
    Real.rpow_add hw.1]
  ring

def currentBudget (Q : CanonicalCovariance.ProfileParameters) (ell : ℝ) (Cs : ℕ→ℝ)
    (k : ℕ) (ρ T A0 ν : ℝ) (q : ℝ≥0) : ℝ :=
  (Ioc (0:ℝ) T).indicator (fun q => (T-q)^(ρ/2)*oldTimeBudget Q ell Cs k T q (1/2:ℝ) A0 ν) q

theorem currentBudget_measurable (Q : CanonicalCovariance.ProfileParameters) (ell : ℝ) (Cs : ℕ→ℝ)
    (k : ℕ) (ρ T A0 ν : ℝ) : Measurable (currentBudget Q ell Cs k ρ T A0 ν) :=
  (((measurable_const.sub measurable_id).pow_const _).mul
    (oldTimeBudget_measurable Q ell Cs k T (1/2:ℝ) A0 ν) |>.indicator measurableSet_Ioc).comp
      measurable_subtype_coe

/-- Original NNReal current-time measure, with no positive-depth or
strictly-positive frequency restriction. -/
theorem currentBudget_memLp (Q : CanonicalCovariance.ProfileParameters) (ell : ℝ) (Cs : ℕ→ℝ)
    (k : ℕ) (ρ T A0 ν : ℝ) (hρ : 0<ρ) (hT : 0<T) (hν : 0≤ν) (H : ℝ≥0) :
    MemLp (currentBudget Q ell Cs k ρ T A0 ν) 2 (timeMeasure H) := by
  have hm : Measurable (fun q : ℝ => (T-q)^(ρ/2)*oldTimeBudget Q ell Cs k T q (1/2:ℝ) A0 ν) :=
    ((measurable_const.sub measurable_id).pow_const _).mul
      (oldTimeBudget_measurable Q ell Cs k T (1/2:ℝ) A0 ν)
  have hw := budget_memLp Q ell Cs k ρ T A0 ν hρ hT hν
  have hwm : Measurable (fun w : ℝ => w^(ρ/2)*oldTimeBudget Q ell Cs k T (T-w) (1/2:ℝ) A0 ν) :=
    (measurable_id.pow_const _).mul
      ((oldTimeBudget_measurable Q ell Cs k T (1/2:ℝ) A0 ν).comp (measurable_const.sub measurable_id))
  have hi : IntervalIntegrable (fun w : ℝ => ‖w^(ρ/2)*oldTimeBudget Q ell Cs k T (T-w) (1/2:ℝ) A0 ν‖^2)
      volume 0 T := (intervalIntegrable_iff_integrableOn_Ioc_of_le hT.le).mpr
        ((memLp_two_iff_integrable_sq_norm hwm.aestronglyMeasurable).mp hw)
  have hj : IntervalIntegrable (fun q : ℝ => ‖(T-q)^(ρ/2)*oldTimeBudget Q ell Cs k T q (1/2:ℝ) A0 ν‖^2)
      volume 0 T := by
    simpa only [sub_zero,sub_self,show ∀ q : ℝ,T-(T-q)=q by intro q;ring] using
      (hi.comp_sub_left T).symm
  have hs := (memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).mpr hj.1
  have hi' := (memLp_indicator_iff_restrict measurableSet_Ioc.nullMeasurableSet).mpr hs
  have hr := hi'.mono_measure (Measure.restrict_le_self (μ:=volume) (s:=Ioc 0 (H:ℝ)))
  have hc : MeasurePreserving ((↑) : ℝ≥0→ℝ) (timeMeasure H) (volume.restrict (Ioc 0 (H:ℝ))) :=
    ⟨measurable_subtype_coe,timeMeasure_map H⟩
  exact hr.comp_measurePreserving hc

end SHE.MeanRMSTimeFactors
