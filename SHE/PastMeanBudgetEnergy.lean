module

public import SHE.PastMeanBudgetClock
public import SHE.SectionEnergy

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHE.PastMeanTimeFactors
open Set MeasureTheory Real PredictableL2
open scoped ENNReal NNReal
variable {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
variable [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

def energyEnvelope (P : CanonicalCovariance.ProfileParameters) (ell : ℝ) (Cs : ℕ→ℝ)
    (k : ℕ) (ρ base T fresh A0 ν K χ : ℝ) (V : ℝ≥0→ℝ) (q : ℝ≥0) : ℝ :=
  (K*(V q)^(χ/2)*currentBudget P ell Cs k ρ base T fresh A0 ν q)^2

theorem energyEnvelope_integrable (P : CanonicalCovariance.ProfileParameters) (ell : ℝ) (Cs : ℕ→ℝ)
    (k : ℕ) (ρ base T fresh A0 ν K χ D : ℝ) (hρ : 0<ρ) (hdegree : 0<ρ+2*fresh-1)
    (hT : base<T) (hν : 0≤ν) (hK : 0≤K) (hχ : 0≤χ) (hD : 0≤D)
    (V : ℝ≥0→ℝ) (hV : Measurable V) (hV0 : ∀ q,0≤V q) (H : ℝ≥0)
    (hb : ∀ q : ℝ≥0,q≤H → base<(q:ℝ) → (q:ℝ)<T → V q≤D) :
    Integrable (energyEnvelope P ell Cs k ρ base T fresh A0 ν K χ V) (timeMeasure H) := by
  have hm:=currentBudget_measurable P ell Cs k ρ base T fresh A0 ν
  have hi:=(memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).mp
    (currentBudget_memLp P ell Cs k ρ base T fresh A0 ν hdegree hT hν H)
  have hi' : Integrable (fun q=>currentBudget P ell Cs k ρ base T fresh A0 ν q^2) (timeMeasure H):=by
    simpa only [Real.norm_eq_abs,sq_abs] using hi
  apply (hi'.const_mul ((K*D^(χ/2))^2)).mono'
    (((measurable_const.mul (hV.pow_const _)).mul hm).pow_const 2).aestronglyMeasurable
  filter_upwards [timeMeasure_ae_mem H] with q hq
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  by_cases ha : base<(q:ℝ) ∧ (q:ℝ)<T
  · have hh : (V q)^(χ/2)≤D^(χ/2):=
      rpow_le_rpow (hV0 q) (hb q hq.2 ha.1 ha.2) (div_nonneg hχ (by norm_num))
    change (K*(V q)^(χ/2)*currentBudget P ell Cs k ρ base T fresh A0 ν q)^2≤_
    rw [mul_pow]
    exact mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (mul_nonneg hK (rpow_nonneg (hV0 q) _))
        (mul_le_mul_of_nonneg_left hh hK) 2) (sq_nonneg _)
  · have hz : currentBudget P ell Cs k ρ base T fresh A0 ν q=0:=by
      unfold currentBudget
      by_cases hm : (q:ℝ)∈Ioc base T
      · have hqT : (q:ℝ)=T:=le_antisymm hm.2 (le_of_not_gt (fun h=>ha ⟨hm.1,h⟩))
        rw [indicator_of_mem hm,hqT,sub_self]
        rw [Real.zero_rpow (ne_of_gt (div_pos hρ (by norm_num))),zero_mul]
      · exact indicator_of_notMem hm _
    simp only [energyEnvelope,Pi.mul_apply,hz,mul_zero,zero_pow (by norm_num : (2:ℕ)≠0),zero_mul,le_refl]

/-- Local current-time/sample energy from the actual old-time RMS
bound. The small current input remains inside the final time integral. -/
theorem energy_product_bound (μ : Measure Ω) [SFinite μ] (H : ℝ≥0)
    (P : CanonicalCovariance.ProfileParameters) (ell : ℝ) (Cs : ℕ→ℝ)
    (k : ℕ) (ρ base T fresh A0 ν K χ D : ℝ) (hρ : 0<ρ) (hdegree : 0<ρ+2*fresh-1)
    (hT : base<T) (hν : 0≤ν) (hK : 0≤K) (hχ : 0≤χ) (hD : 0≤D)
    (V : ℝ≥0→ℝ) (hV : Measurable V) (hV0 : ∀ q,0≤V q)
    (hb : ∀ q : ℝ≥0,q≤H → base<(q:ℝ) → (q:ℝ)<T → V q≤D)
    (F : ℝ≥0×Ω→E) (hF : Measurable F)
    (hs : ∀ q : ℝ≥0,q≤H → base<(q:ℝ) → (q:ℝ)<T →
      Integrable (fun ω=>‖F (q,ω)‖^2) μ ∧
        (∫ ω,‖F (q,ω)‖^2 ∂μ)≤
          (K*(V q)^(χ/2)*(T-q)^(ρ/2)*
            QuarterRMSTimeFactors.oldTimeBudget P ell Cs k (T-base) (q-base) fresh A0 ν)^2)
    (hz : ∀ q : ℝ≥0,¬(base<(q:ℝ) ∧ (q:ℝ)<T) → ∀ ω,F (q,ω)=0) :
    Integrable (fun z=>‖F z‖^2) (energyMeasure μ H) ∧
      (∫ z,‖F z‖^2 ∂energyMeasure μ H)≤
        ∫ q,energyEnvelope P ell Cs k ρ base T fresh A0 ν K χ V q ∂timeMeasure H := by
  have hsec : ∀ᵐ q ∂timeMeasure H,Integrable (fun ω=>‖F (q,ω)‖^2) μ ∧
      (∫ ω,‖F (q,ω)‖^2 ∂μ)≤energyEnvelope P ell Cs k ρ base T fresh A0 ν K χ V q := by
    filter_upwards [timeMeasure_ae_mem H] with q hq
    by_cases ha : base<(q:ℝ) ∧ (q:ℝ)<T
    · have hh:=hs q hq.2 ha.1 ha.2
      refine ⟨hh.1,?_⟩
      rw [energyEnvelope,currentBudget,indicator_of_mem (show (q:ℝ)∈Ioc base T from ⟨ha.1,ha.2.le⟩)]
      simpa only [mul_assoc] using hh.2
    · have hzero:=hz q ha
      constructor
      · convert! integrable_zero Ω ℝ μ using 1
        funext ω
        simp only [hzero,norm_zero,zero_pow (by norm_num : (2:ℕ)≠0),Pi.zero_apply]
      · simpa only [hzero,norm_zero,zero_pow (by norm_num : (2:ℕ)≠0),integral_zero,energyEnvelope] using
          sq_nonneg (K*(V q)^(χ/2)*currentBudget P ell Cs k ρ base T fresh A0 ν q)
  exact SectionEnergy.product_energy μ (timeMeasure H) F hF _
    (energyEnvelope_integrable P ell Cs k ρ base T fresh A0 ν K χ D
      hρ hdegree hT hν hK hχ hD V hV hV0 H hb)
    (hsec.mono (fun _ h=>h.1)) (hsec.mono (fun _ h=>h.2))

end SHE.PastMeanTimeFactors
