module

public import SHE.MeanBudgetSquare
public import SHE.SectionEnergy
public import SHE.PredictableTime

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHE.MeanBudgetEnergy
open Set MeasureTheory Real PredictableL2 PhysicalAssignmentGapScale MeanRMSTimeFactors
open QuarterRMSTimeFactors (oldTimeBudget)
open scoped ENNReal NNReal
variable {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
variable [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

def envelope (Q : CanonicalCovariance.ProfileParameters) (ell : ℝ) (Cs : ℕ→ℝ)
    (k : ℕ) (ρ T A0 ν K χ : ℝ) (V : ℝ≥0→ℝ) (q : ℝ≥0) : ℝ :=
  (K*(V q)^(χ/2)*currentBudget Q ell Cs k ρ T A0 ν q)^2

/-- The actual mean-input current-time envelope is integrable for
every finite depth. A uniform input moment is only used on the active
current-time interval; the quantitative energy keeps its actual value. -/
theorem envelope_integrable (Q : CanonicalCovariance.ProfileParameters) (ell : ℝ) (Cs : ℕ→ℝ)
    (k : ℕ) (ρ T A0 ν K χ D : ℝ) (hρ : 0<ρ) (hT : 0<T) (hν : 0≤ν)
    (hK : 0≤K) (hχ : 0≤χ) (hD : 0≤D) (V : ℝ≥0→ℝ) (hV : Measurable V)
    (hV0 : ∀ q,0≤V q) (H : ℝ≥0)
    (hb : ∀ q : ℝ≥0,q≤H → (q:ℝ)<T → V q≤D) :
    Integrable (envelope Q ell Cs k ρ T A0 ν K χ V) (timeMeasure H) := by
  have hm := currentBudget_measurable Q ell Cs k ρ T A0 ν
  have hi := (memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).mp
    (currentBudget_memLp Q ell Cs k ρ T A0 ν hρ hT hν H)
  have hi' : Integrable (fun q => currentBudget Q ell Cs k ρ T A0 ν q^2) (timeMeasure H) := by
    simpa only [Real.norm_eq_abs,sq_abs] using hi
  apply (hi'.const_mul ((K*D^(χ/2))^2)).mono'
    (((measurable_const.mul (hV.pow_const _)).mul hm).pow_const 2).aestronglyMeasurable
  filter_upwards [timeMeasure_ae_mem H] with q hq
  change ‖(K*(V q)^(χ/2)*currentBudget Q ell Cs k ρ T A0 ν q)^2‖≤_
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  by_cases hqT : (q:ℝ)<T
  · have hh : (V q)^(χ/2)≤D^(χ/2) :=
      Real.rpow_le_rpow (hV0 q) (hb q hq.2 hqT) (div_nonneg hχ (by norm_num))
    rw [mul_pow]
    exact mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (mul_nonneg hK (rpow_nonneg (hV0 q) _))
        (mul_le_mul_of_nonneg_left hh hK) 2) (sq_nonneg _)
  · have hz : currentBudget Q ell Cs k ρ T A0 ν q=0 :=
      by
        unfold currentBudget
        by_cases hm : (q:ℝ)∈Ioc 0 T
        · rw [Set.indicator_of_mem hm,show (q:ℝ)=T from le_antisymm hm.2 (le_of_not_gt hqT),sub_self,
            Real.zero_rpow (by linarith : ρ/2≠0),zero_mul]
        · exact Set.indicator_of_notMem hm _
    simp only [hz,mul_zero,zero_pow (by norm_num : (2:ℕ)≠0)]
    exact le_rfl

/-- A section estimate for the actual old-time average gives genuine
joint current-time/sample energy, without any stochastic Fubini input. -/
theorem product_bound (μ : Measure Ω) [SFinite μ] (H : ℝ≥0)
    (Q : CanonicalCovariance.ProfileParameters) (ell : ℝ) (Cs : ℕ→ℝ)
    (k : ℕ) (ρ T A0 ν K χ D : ℝ) (hρ : 0<ρ) (hT : 0<T) (hν : 0≤ν)
    (hK : 0≤K) (hχ : 0≤χ) (hD : 0≤D) (V : ℝ≥0→ℝ) (hV : Measurable V)
    (hV0 : ∀ q,0≤V q) (hb : ∀ q : ℝ≥0,q≤H → (q:ℝ)<T → V q≤D)
    (F : ℝ≥0×Ω→E) (hF : Measurable F)
    (hs : ∀ q : ℝ≥0,q≤H → (q:ℝ)<T →
      Integrable (fun ω => ‖F (q,ω)‖^2) μ ∧
      (∫ ω,‖F (q,ω)‖^2 ∂μ)≤
        (K*(T-q)^(ρ/2)*(V q)^(χ/2)*oldTimeBudget Q ell Cs k T q (1/2:ℝ) A0 ν)^2)
    (hz : ∀ q : ℝ≥0,T≤(q:ℝ) → ∀ ω,F (q,ω)=0) :
    Integrable (fun z => ‖F z‖^2) (energyMeasure μ H) ∧
      (∫ z,‖F z‖^2 ∂energyMeasure μ H)≤
        ∫ q,envelope Q ell Cs k ρ T A0 ν K χ V q ∂timeMeasure H := by
  have hsec : ∀ᵐ q ∂timeMeasure H,Integrable (fun ω => ‖F (q,ω)‖^2) μ ∧
      (∫ ω,‖F (q,ω)‖^2 ∂μ)≤envelope Q ell Cs k ρ T A0 ν K χ V q := by
    filter_upwards [timeMeasure_ae_mem H] with q hq
    by_cases hqT : (q:ℝ)<T
    · have hp := hs q hq.2 hqT
      refine ⟨hp.1,?_⟩
      have hq0 : (0:ℝ)<q := by exact_mod_cast hq.1
      change (∫ ω,‖F (q,ω)‖^2 ∂μ)≤_
      have he : envelope Q ell Cs k ρ T A0 ν K χ V q=
          (K*(T-q)^(ρ/2)*(V q)^(χ/2)*oldTimeBudget Q ell Cs k T q (1/2:ℝ) A0 ν)^2 := by
        rw [envelope,currentBudget,Set.indicator_of_mem (show (q:ℝ)∈Ioc (0:ℝ) T from ⟨hq0,hqT.le⟩)]
        ring
      rw [he]
      exact hp.2
    · have hzero := hz q (le_of_not_gt hqT)
      constructor
      · convert! integrable_zero Ω ℝ μ using 1
        funext ω
        simp only [hzero,norm_zero,zero_pow (by norm_num : (2:ℕ)≠0),Pi.zero_apply]
      · simpa only [hzero,norm_zero,zero_pow (by norm_num : (2:ℕ)≠0),integral_zero,envelope] using
          sq_nonneg (K*(V q)^(χ/2)*currentBudget Q ell Cs k ρ T A0 ν q)
  exact SectionEnergy.product_energy μ (timeMeasure H) F hF _
    (envelope_integrable Q ell Cs k ρ T A0 ν K χ D hρ hT hν hK hχ hD V hV hV0 H hb)
    (hsec.mono (fun _ h=>h.1)) (hsec.mono (fun _ h=>h.2))

end SHE.MeanBudgetEnergy
