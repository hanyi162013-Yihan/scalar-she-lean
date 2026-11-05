module

public import SHE.MixedJointMarkLimit
public import SHE.JointRecursiveHessian
public import SHE.NativeRowTargetContinuity
public import SHE.MixedNativeJointHistory
public import SHE.JointInsertionIntegrability
public import SHE.JointWordDefect

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
set_option quotPrecheck false
noncomputable section

namespace SHE.MixedJointMarkConvergence
open MeasureTheory Set PredictableL2 NativeHeatObservation NativeObservationNaturality
open FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation CutoffWordLevel
open GaussianTaylorAverage JointWordAnalytic
open scoped ENNReal NNReal
local instance mixedJointMarkConvergenceInstance1 : Fact (0<(1:ℝ)) := ⟨zero_lt_one⟩
local instance mixedJointMarkConvergenceInstance2 : Fact (0<2*Real.pi) := ⟨by positivity⟩
local instance mixedJointMarkConvergenceInstance3 : MeasurableSpace CircleHeat.CircleL2 := borel _
local instance mixedJointMarkConvergenceInstance4 : BorelSpace CircleHeat.CircleL2 := ⟨rfl⟩
local instance mixedJointMarkConvergenceInstance5 : MeasurableSpace CircleL2 := borel _
local instance mixedJointMarkConvergenceInstance6 : BorelSpace CircleL2 := ⟨rfl⟩
local instance mixedJointMarkConvergenceInstance7 : MeasurableSpace RealL2 := borel _
local instance mixedJointMarkConvergenceInstance8 : BorelSpace RealL2 := ⟨rfl⟩
variable {Ω P : Type*} [MeasurableSpace Ω] [MeasurableSpace P]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
variable (Λ κ : ℝ) (hκ : 0<κ) {aU aV : ℝ→ℝ} (haU : Measurable aU) (haV : Measurable aV) {ell M : ℝ}
variable (hell : 0<ell) (hbU : ∀ z,ell≤aU z ∧ aU z≤M) (hbV : ∀ z,ell≤aV z ∧ aV z≤M)
variable (I₀ I₁ : StandardTerminalIto (C := RealHaarIntegrand.Columns) (E := RealL2) 𝓕 μ H)
variable (u₀ v₀ : RealL2)
variable (S : MixedNativeAdditiveResidualPair.Solution 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀)
variable {R : ReferenceData} {n : ℕ} (L : Level R P n)
local notation "dU" => MixedNativeJointHistory.firstData 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
local notation "dV" => MixedNativeJointHistory.secondData 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
local notation "U" => (dU).physicalState
local notation "V" => (dV).physicalState
local notation "XU" => (dU).physicalField
local notation "XV" => (dV).physicalField

open CutoffWordHistories RecursiveHeatBounds RecursiveHeatTargets Filter Topology
variable (δ : ℝ) (hδ : 0<δ)

local notation "Mmark" => MixedJointMarkLimit.mark 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S L δ hδ
local notation "D" => MixedJointLevelData.defect 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
local notation "I" => fun ε k => JointWordDefect.integrand (level L δ hδ ε k) Λ U V XU XV (D (level L δ hδ ε k))

/-- Epsilon-uniform mark mass is proved by integrating the actual
endpoint heat-square majorant. Constants retain fixed smooth depth/delta. -/
theorem uniform_mark_bound (hΛ : 0≤Λ) (k : ℕ) : ∃ K : ℝ,0≤K ∧ ∀ ε : ℝ≥0,∀ p ω,
    ‖Mmark ε k p ω‖≤K := by
  obtain ⟨K,hK,hKb⟩ := MixedJointMarkLimit.uniform_integrand_bound 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S L δ hδ hΛ k
  refine ⟨K*PhysicalRemainderMass.heatMass R.horizon,
    mul_nonneg hK (PhysicalRemainderMass.heatMass_nonneg (R.base_nonneg.trans R.ordered)),fun ε p ω => ?_⟩
  let s := (level L δ hδ 0 k).terminal p
  have hs : R.base≤s := (level L δ hδ 0 k).terminal_base p
  have hd : IntervalIntegrable (fun t => K*(1+heatConstant*(s-t)^(-(1/2:ℝ)))) volume R.base s :=
    CovarianceEndpoint.endpoint_majorant_integrable K
  have hdom : ∀ᵐ t ∂volume, t∈Ioc R.base s → ‖I ε k ((p,ω),t)‖≤K*(1+heatConstant*(s-t)^(-(1/2:ℝ))) := by
    filter_upwards [volume.ae_ne s] with t hne ht
    exact hKb ε p ω t ⟨ht.1,lt_of_le_of_ne ht.2 hne⟩
  have hb := intervalIntegral.norm_integral_le_of_norm_le hs hdom hd
  rw [intervalIntegral.integral_const_mul,PhysicalRemainderMass.heat_majorant_mass hs] at hb
  change ‖∫ t in R.base..(level L δ hδ ε k).terminal p,I ε k ((p,ω),t)‖≤_
  rw [terminal_eq L δ hδ ε 0 k p]
  exact hb.trans (mul_le_mul_of_nonneg_left (PhysicalRemainderMass.heatMass_mono (sub_nonneg.mpr hs)
    (by dsimp [s]; linarith [R.base_nonneg,(level L δ hδ 0 k).terminal_horizon p])) hK)

/-- The retained first-defect mark is continuous through zero heat age.
The actual coefficients need only be measurable in time. -/
theorem continuous_mark (hΛ : 0≤Λ) (k : ℕ) (p : History P k) (ω : Ω) :
    Continuous (fun ε : ℝ≥0 => Mmark ε k p ω) := by
  obtain ⟨K,hK,hKb⟩ := MixedJointMarkLimit.uniform_integrand_bound 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S L δ hδ hΛ k
  let s := (level L δ hδ 0 k).terminal p
  have hs : R.base≤s := (level L δ hδ 0 k).terminal_base p
  have he : (fun ε : ℝ≥0 => Mmark ε k p ω)=fun ε =>
      ∫ t,I ε k ((p,ω),t) ∂volume.restrict (Ioc R.base s) := by
    funext ε
    change (∫ t in R.base..(level L δ hδ ε k).terminal p,I ε k ((p,ω),t))=_
    rw [terminal_eq L δ hδ ε 0 k p,intervalIntegral.integral_of_le hs]
  rw [he]
  apply continuous_of_dominated (bound := fun t : ℝ => K*(1+heatConstant*(s-t)^(-(1/2:ℝ))))
  · intro ε
    exact ((JointWordDefect.integrand_measurable (level L δ hδ ε k) Λ
      (dU).physicalState_measurable (dV).physicalState_measurable
      (dU).physicalField_measurable (dV).physicalField_measurable
      (MixedJointLevelData.defect_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S (level L δ hδ ε k))).comp
      ((measurable_const (a := (p,ω))).prodMk measurable_id)).aestronglyMeasurable
  · intro ε
    filter_upwards [ae_restrict_mem measurableSet_Ioc,ae_restrict_of_ae (volume.ae_ne s)] with t ht hne
    exact hKb ε p ω t ⟨ht.1,lt_of_le_of_ne ht.2 hne⟩
  · exact (CovarianceEndpoint.endpoint_majorant_integrable (q := R.base) (s := s) K).1
  · filter_upwards [ae_restrict_mem measurableSet_Ioc,ae_restrict_of_ae (volume.ae_ne s)] with t ht hne
    exact MixedJointMarkLimit.continuous_integrand 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S L δ hδ k p ω
      ⟨ht.1,lt_of_le_of_ne ht.2 hne⟩

/-- Full history/sample L1 convergence of the actual mixed common-Haar
first-defect marks, not only a fixed observation or fixed test limit. -/
theorem integrated_mark_difference_tendsto_zero (hΛ : 0≤Λ)
    (ν : Measure P) [IsFiniteMeasure ν] (k : ℕ) :
    Tendsto (fun ε : ℝ => ∫ q : History P k×Ω,
      |Mmark ε.toNNReal k q.1 q.2-Mmark 0 k q.1 q.2| ∂(historyMeasure R ν k).prod μ)
      (𝓝[>] (0:ℝ)) (𝓝 0) := by
  obtain ⟨K,hK,hKb⟩ := uniform_mark_bound 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S L δ hδ hΛ k
  have hm (ε : ℝ) : Measurable (fun q : History P k×Ω =>
      |Mmark ε.toNNReal k q.1 q.2-Mmark 0 k q.1 q.2|) :=
    ((MixedJointLevelData.mark_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S (level L δ hδ ε.toNNReal k)).sub
      (MixedJointLevelData.mark_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S (level L δ hδ 0 k))).norm
  have ht (q : History P k×Ω) : Tendsto (fun ε : ℝ =>
      |Mmark ε.toNNReal k q.1 q.2-Mmark 0 k q.1 q.2|) (𝓝[>] (0:ℝ)) (𝓝 0) := by
    have hc := (continuous_mark 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S L δ hδ hΛ k q.1 q.2).comp continuous_real_toNNReal
    have hh := ((hc.tendsto (0:ℝ)).sub_const (Mmark 0 k q.1 q.2)).norm
    simpa only [Function.comp_def,Real.toNNReal_zero,sub_self,norm_zero,Real.norm_eq_abs] using
      hh.mono_left (nhdsWithin_le_nhds (s := Ioi (0:ℝ)))
  have hi := tendsto_integral_filter_of_dominated_convergence (μ := (historyMeasure R ν k).prod μ)
    (fun _ => 2*K) (Eventually.of_forall (fun ε => (hm ε).aestronglyMeasurable))
    (Eventually.of_forall (fun ε => Eventually.of_forall (fun q => by
      rw [Real.norm_eq_abs,abs_abs]
      exact (norm_sub_le _ _).trans ((add_le_add (hKb ε.toNNReal q.1 q.2) (hKb 0 q.1 q.2)).trans_eq (by ring)))))
    (integrable_const _) (Eventually.of_forall ht)
  simpa only [integral_zero] using hi

end SHE.MixedJointMarkConvergence
