module

public import SHE.NativeObservationProcess
public import SHE.CovarianceEndpoint
public import SHE.PredictableTime

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-! Actual predictable square-integrable observation rows through zero
terminal heat age. Predictability is obtained from a true pointwise
limit of positive-gap observations; energy uses the integrable native
heat singularity (T-r)^(-1/2), rather than an assumed gap bound. -/
noncomputable section
namespace SHE.NativeObservationEndpoint
open Set MeasureTheory ProbabilityTheory Filter StoppedFourier CovarianceEndpoint
open FiniteHaar NativeHeatObservation NativeObservationCovariance NativeObservationProcess PredictableL2
open scoped NNReal ENNReal Topology
local instance nativeObservationEndpoint_unitPositive : Fact (0 < (1:ℝ)) := ⟨zero_lt_one⟩
local instance nativeObservationEndpoint_periodPositive : Fact (0 < 2*Real.pi) := ⟨by positivity⟩
local instance nativeObservationEndpoint_finiteExponent : Fact ((2:ENNReal) ≠ ⊤) := ⟨by simp⟩
local instance nativeObservationEndpoint_circleSigma : MeasurableSpace CircleHeat.CircleL2 := borel CircleHeat.CircleL2
local instance nativeObservationEndpoint_circleBorel : BorelSpace CircleHeat.CircleL2 := ⟨rfl⟩
local instance nativeObservationEndpoint_rowSigma : MeasurableSpace RealHaarInput := borel RealHaarInput
local instance nativeObservationEndpoint_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
variable {Ω : Type*} [MeasurableSpace Ω]

def approach (T : ℝ) (n : ℕ) : ℝ := T-1/((n:ℝ)+1)
theorem approach_lt (T : ℝ) (n : ℕ) : approach T n < T := by
  unfold approach
  have hp : 0 < 1/((n:ℝ)+1) := by positivity
  linarith
theorem approach_tendsto (T : ℝ) : Tendsto (approach T) atTop (𝓝 T) := by
  change Tendsto (fun n : ℕ => T-1/((n:ℝ)+1)) atTop (𝓝 T)
  simpa only [sub_zero] using (tendsto_const_nhds (x := T)).sub
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))

def fullIntegrand {ell M : ℝ} (hell : 0 < ell) (f : ℝ≥0 × Ω → EllipticField ell M)
    (T : ℝ) (x : HeatCircle) (p : ℝ≥0 × Ω) : RealHaarInput :=
  if (p.1:ℝ) < T then row hell (f p) T (p.1:ℝ) x else 0

theorem integrand_tendsto {ell M : ℝ} (hell : 0 < ell) (f : ℝ≥0 × Ω → EllipticField ell M)
    (T : ℝ) (x : HeatCircle) (p : ℝ≥0 × Ω) :
    Tendsto (fun n => integrand hell f T (approach T n) x p) atTop (𝓝 (fullIntegrand hell f T x p)) := by
  by_cases hp : (p.1:ℝ) < T
  · have he := (approach_tendsto T).eventually (lt_mem_nhds hp)
    apply tendsto_const_nhds.congr'
    filter_upwards [he] with n hn
    rw [integrand_eq hell f (approach_lt T n),ite_eq_left hn,fullIntegrand,ite_eq_left hp]
  · have he : ∀ n, integrand hell f T (approach T n) x p=0 := by
      intro n
      rw [integrand_eq hell f (approach_lt T n),ite_eq_right]
      exact not_lt.mpr ((approach_lt T n).le.trans (le_of_not_gt hp))
    simp only [he,fullIntegrand,ite_eq_right hp]
    exact tendsto_const_nhds

theorem fullIntegrand_predictable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›)
    {ell M : ℝ} (hell : 0 < ell) {f : ℝ≥0 × Ω → EllipticField ell M}
    (hf : StronglyMeasurable[𝓕.predictable] f) (T : ℝ) (x : HeatCircle) :
    StronglyMeasurable[𝓕.predictable] (fullIntegrand hell f T x) := by
  apply stronglyMeasurable_of_tendsto atTop
    (fun n => integrand_predictable 𝓕 hell hf T (approach T n) x)
  exact tendsto_pi_nhds.mpr (fun p => integrand_tendsto hell f T x p)

theorem majorant_integrable (μ : Measure Ω) [IsProbabilityMeasure μ] (h : ℝ≥0)
    (M T : ℝ) (hT : (h:ℝ) ≤ T) :
    Integrable (fun p : ℝ≥0 × Ω => M*(1+heatConstant*(T-(p.1:ℝ))^(-(1/2:ℝ)))) (energyMeasure μ h) := by
  have hT0 : 0 ≤ T := h.2.trans hT
  have hi : IntervalIntegrable (fun r : ℝ => M*(1+heatConstant*(T-r)^(-(1/2:ℝ)))) volume 0 T :=
    endpoint_majorant_integrable M
  have hih := hi.mono_set (c := 0) (d := (h:ℝ))
    (uIcc_subset_uIcc left_mem_uIcc (mem_uIcc_of_le h.2 hT))
  have hig : Integrable (fun r : ℝ => M*(1+heatConstant*(T-r)^(-(1/2:ℝ))))
      (volume.restrict (Ioc 0 (h:ℝ))) := (intervalIntegrable_iff_integrableOn_Ioc_of_le h.2).mp hih
  have hit : Integrable (fun r : ℝ≥0 => M*(1+heatConstant*(T-(r:ℝ))^(-(1/2:ℝ)))) (timeMeasure h) :=
    ((timeMeasurePreserving h).integrable_comp_emb nonnegative_coe_measurableEmbedding).mpr hig
  exact hit.comp_fst μ

theorem fullIntegrand_memLp (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›)
    (μ : Measure Ω) [IsProbabilityMeasure μ] (h : ℝ≥0)
    {ell M : ℝ} (hell : 0 < ell) (hM : 0 ≤ M)
    {f : ℝ≥0 × Ω → EllipticField ell M} (hf : StronglyMeasurable[𝓕.predictable] f)
    {T : ℝ} (hT : (h:ℝ) ≤ T) (x : HeatCircle) :
    @MemLp _ _ 𝓕.predictable _ _ (fullIntegrand hell f T x) 2
      ((energyMeasure μ h).trim (predictable_le_product 𝓕)) := by
  have hp := fullIntegrand_predictable 𝓕 hell hf T x
  have hm := hp.mono (predictable_le_product 𝓕)
  have hsq : Integrable (fun p => ‖fullIntegrand hell f T x p‖^2) (energyMeasure μ h) := by
    apply (majorant_integrable μ h M T hT).mono' (hm.norm.pow 2).aestronglyMeasurable
    have htime : ∀ᵐ p ∂energyMeasure μ h,(p.1:ℝ) ≤ (h:ℝ) := by
      have he : ∀ᵐ (s : ℝ≥0) ∂timeMeasure h,(s:ℝ) ≤ (h:ℝ) :=
        (timeMeasure_ae_mem h).mono (fun s hs => by exact_mod_cast hs.2)
      exact (Measure.quasiMeasurePreserving_fst (μ := timeMeasure h) (ν := μ)).ae he
    filter_upwards [htime] with p hph
    change ‖‖fullIntegrand hell f T x p‖^2‖ ≤ _
    rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
    unfold fullIntegrand
    split_ifs with ht
    · exact row_norm_sq_bound hell (f p) ht le_rfl x
    · simp only [norm_zero,zero_pow (by norm_num : (2:ℕ) ≠ 0)]
      exact mul_nonneg hM (add_nonneg zero_le_one (mul_nonneg heatConstant_pos.le
        (Real.rpow_nonneg (sub_nonneg.mpr (hph.trans hT)) _)))
  have hmem : MemLp (fullIntegrand hell f T x) 2 (energyMeasure μ h) :=
    (memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).mpr hsq
  change eLpNorm (fullIntegrand hell f T x) 2 ((energyMeasure μ h).trim (predictable_le_product 𝓕)) < ∞
  rw [eLpNorm_trim (predictable_le_product 𝓕) hp]
  exact hmem

def process (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›)
    (μ : Measure Ω) [IsProbabilityMeasure μ] (h : ℝ≥0)
    {ell M : ℝ} (hell : 0 < ell) (hM : 0 ≤ M)
    (f : ℝ≥0 × Ω → EllipticField ell M) (hf : StronglyMeasurable[𝓕.predictable] f)
    {T : ℝ} (hT : (h:ℝ) ≤ T) (x : HeatCircle) : Process (E := RealHaarInput) 𝓕 μ h :=
  (fullIntegrand_memLp 𝓕 μ h hell hM hf hT x).toLp (fullIntegrand hell f T x)

theorem process_ae (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›)
    (μ : Measure Ω) [IsProbabilityMeasure μ] (h : ℝ≥0)
    {ell M : ℝ} (hell : 0 < ell) (hM : 0 ≤ M)
    (f : ℝ≥0 × Ω → EllipticField ell M) (hf : StronglyMeasurable[𝓕.predictable] f)
    {T : ℝ} (hT : (h:ℝ) ≤ T) (x : HeatCircle) :
    process 𝓕 μ h hell hM f hf hT x =ᵐ[energyMeasure μ h] fullIntegrand hell f T x :=
  ae_eq_of_ae_eq_trim (fullIntegrand_memLp 𝓕 μ h hell hM hf hT x).coeFn_toLp

end SHE.NativeObservationEndpoint
