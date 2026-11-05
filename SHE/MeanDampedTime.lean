module

public import SHE.MeanBudgetSquare
public import SHE.NegativeL2Heat
public import SHE.QuarterRMSFields

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHE.MeanRMSTimeFactors
open Set MeasureTheory Real PhysicalAssignmentGapScale GaussianAssignmentBlocks AssignmentGapPartition
  AllocatedAssignmentKernel CoveredHistoryGeometry QuarterRMSTimeFactors PredictableL2
  WordRecursion CutoffWordLevel CutoffWordHistories CutoffCarriers HistoryProductMeasure
  QuarterSpatialEvent PhysicalParentGeometry
  PhysicalScoreChain
open scoped ENNReal NNReal BigOperators
local instance meanDampedTime_finiteExponent : Fact ((2:ℝ≥0∞)≠⊤) := ⟨by simp⟩

/-- A retained quarter-row exponential buys any chosen fractional
fresh-gap degree, with an explicit damping power. -/
theorem damping_power_bound {Λ d ε : ℝ} (hΛ : 0<Λ) (hd : 0<d)
    (hε : 0≤ε) (hε1 : ε≤1) :
    exp (-Λ*d/4)≤(4:ℝ)^ε*Λ^(-ε)*d^(-ε) := by
  have hk : 0<d/4 := by positivity
  have hb := NegativeL2Heat.polynomial_heat_bound hΛ hk.le hε hε1
  have hp : (d/4)^ε*(d/4)^(-ε)=1 := by
    rw [←Real.rpow_add hk]
    simp only [add_neg_cancel,Real.rpow_zero]
  have hh := mul_le_mul_of_nonneg_right hb (rpow_nonneg hk.le (-ε))
  have he : (d/4)^(-ε)=d^(-ε)*(4:ℝ)^ε := by
    rw [Real.div_rpow hd.le (by norm_num : (0:ℝ)≤4),div_eq_mul_inv,←Real.rpow_neg (by norm_num : (0:ℝ)≤4),neg_neg]
  calc
    _=exp (-Λ*(d/4))*((d/4)^ε*(d/4)^(-ε)) := by rw [hp];congr 1;ring
    _≤Λ^(-ε)*(d/4)^(-ε) := by convert! hh using 1 <;> ring
    _=_ := by rw [he];ring

variable {R : ReferenceData} (L : CutoffWordLevel.Level R StoppedFourier.HeatCircle 1)

/-- No new old-time estimate is assumed: the retained exponential is
inserted in the literal sharp finite-word density before averaging. -/
theorem damped_integrand_bound (Q : CanonicalCovariance.ProfileParameters)
    {ell : ℝ} (hell : 0<ell) (Cs : ℕ→ℝ) (hCs : ∀ j,0≤Cs j)
    (k : ℕ) (q A0 ν Λ ε : ℝ) (hΛ : 0<Λ) (hε : 0≤ε) (hε1 : ε≤1)
    (p : History StoppedFourier.HeatCircle k) :
    exp (-Λ*((carrier L k).terminal p-q)/4)*
      totalIntegrand L Q ell Cs k q (1/2:ℝ) A0 ν p≤
      ((4:ℝ)^ε*Λ^(-ε))*totalIntegrand L Q ell Cs k q (1/2-ε) A0 ν p := by
  unfold totalIntegrand
  split_ifs with ha
  · have hd : 0<(carrier L k).terminal p-q := sub_pos.mpr ha.2
    have hB : 0≤timeWeight L ell Cs k p*SharpWordTimeScale.total L Q k p q A0 ν :=
      mul_nonneg (timeWeight_nonneg L hell Cs hCs k p ha.1) (SharpWordTimeScale.total_nonneg L Q k p q A0 ν)
    have hb := mul_le_mul_of_nonneg_right (damping_power_bound hΛ hd hε hε1)
      (mul_nonneg (rpow_nonneg hd.le ((1/2:ℝ)-1)) hB)
    have hp : ((carrier L k).terminal p-q)^(-ε)*((carrier L k).terminal p-q)^((1/2:ℝ)-1)=
        ((carrier L k).terminal p-q)^((1/2:ℝ)-ε-1) := by
      rw [←Real.rpow_add hd]
      congr 1
      ring
    calc
      _=exp (-Λ*((carrier L k).terminal p-q)/4)*
          (((carrier L k).terminal p-q)^((1/2:ℝ)-1)*
            (timeWeight L ell Cs k p*SharpWordTimeScale.total L Q k p q A0 ν)) := by ring
      _≤_ := hb
      _=_ := by rw [←hp];ring
  · simp only [mul_zero,le_refl]

theorem damped_old_time_budget (Q : CanonicalCovariance.ProfileParameters)
    (T : ℝ) (hT : ∀ p,L.terminal p=T) {ell : ℝ} (hell : 0<ell)
    (Cs : ℕ→ℝ) (hCs : ∀ j,0≤Cs j) (k : ℕ)
    {q A0 ν Λ ε : ℝ} (hqbase : R.base≤q) (hqT : q<T) (hTH : T≤R.horizon)
    (hA0 : 0≤A0) (hν : 0≤ν) (hΛ : 0<Λ) (hε : 0≤ε) (hεhalf : ε<1/2) :
    Integrable (fun t=>exp (-Λ*((carrier L k).terminal (anchor k t)-q)/4)*
      totalIntegrand L Q ell Cs k q (1/2:ℝ) A0 ν (anchor k t))
      (Measure.pi (fun _ : Fin k=>volume.restrict (Ioc R.base R.horizon))) ∧
    (∫ t,exp (-Λ*((carrier L k).terminal (anchor k t)-q)/4)*
      totalIntegrand L Q ell Cs k q (1/2:ℝ) A0 ν (anchor k t)
      ∂Measure.pi (fun _ : Fin k=>volume.restrict (Ioc R.base R.horizon)))≤
      ((4:ℝ)^ε*Λ^(-ε))*oldTimeBudget Q ell Cs k T q (1/2-ε) A0 ν := by
  have hb := total_old_time_budget L Q T hT hell Cs hCs k hqbase hqT hTH
    (by linarith : 0<(1/2:ℝ)-ε) (by linarith : (1/2:ℝ)-ε≤1) hA0 hν
  have hcoef : 0≤(4:ℝ)^ε*Λ^(-ε) := mul_nonneg (rpow_nonneg (by norm_num) _) (rpow_nonneg hΛ.le _)
  have hm : Measurable (fun t=>exp (-Λ*((carrier L k).terminal (anchor k t)-q)/4)*
      totalIntegrand L Q ell Cs k q (1/2:ℝ) A0 ν (anchor k t)) := by
    apply Measurable.mul
    · exact ((((carrier L k).terminal_measurable.comp (anchor_measurable k)).sub measurable_const).const_mul (-Λ)).div_const 4 |>.exp
    · exact (QuarterRMSTimeFactors.totalIntegrand_joint_measurable L Q ell Cs k (1/2:ℝ) A0 ν).comp
        (measurable_const.prodMk (anchor_measurable k))
  have hn (t : Fin k→ℝ) : 0≤exp (-Λ*((carrier L k).terminal (anchor k t)-q)/4)*
      totalIntegrand L Q ell Cs k q (1/2:ℝ) A0 ν (anchor k t) :=
    mul_nonneg (exp_pos _).le (totalIntegrand_nonneg L Q hell Cs hCs k q (1/2:ℝ) A0 ν _)
  have hbound (t : Fin k→ℝ) := damped_integrand_bound L Q hell Cs hCs k q A0 ν Λ ε hΛ hε (by linarith) (anchor k t)
  have hi := (hb.1.const_mul ((4:ℝ)^ε*Λ^(-ε))).mono' hm.aestronglyMeasurable
    (ae_of_all _ (fun t=>by rw [Real.norm_of_nonneg (hn t)];exact hbound t))
  refine ⟨hi,?_⟩
  have hh := integral_mono hi (hb.1.const_mul ((4:ℝ)^ε*Λ^(-ε))) hbound
  rw [integral_const_mul] at hh
  exact hh.trans (mul_le_mul_of_nonneg_left hb.2 hcoef)

end SHE.MeanRMSTimeFactors
