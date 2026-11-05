module

public import SHE.NativeObservationCovariance
public import SHE.StandardTerminalIto
public import SHE.PredictableClock

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-! Genuine predictable L² integrands for native physical heat
observations before their original targets. They are constructed from
the actual common-Haar heat columns, rather than supplied noise rows. -/
noncomputable section
namespace SHE.NativeObservationProcess
open Set MeasureTheory ProbabilityTheory StoppedFourier
open FiniteHaar DyadicApproximation NativeHeatObservation NativeObservationCovariance PredictableL2
open scoped NNReal ENNReal
local instance nativeObservationProcess_unitPositive : Fact (0 < (1:ℝ)) := ⟨zero_lt_one⟩
local instance nativeObservationProcess_periodPositive : Fact (0 < 2*Real.pi) := ⟨by positivity⟩
local instance nativeObservationProcess_finiteExponent : Fact ((2:ENNReal) ≠ ⊤) := ⟨by simp⟩
local instance nativeObservationProcess_circleSigma : MeasurableSpace CircleHeat.CircleL2 := borel CircleHeat.CircleL2
local instance nativeObservationProcess_circleBorel : BorelSpace CircleHeat.CircleL2 := ⟨rfl⟩
local instance nativeObservationProcess_columnsSigma : MeasurableSpace RealHaarIntegrand.Columns := borel RealHaarIntegrand.Columns
local instance nativeObservationProcess_columnsBorel : BorelSpace RealHaarIntegrand.Columns := ⟨rfl⟩
local instance nativeObservationProcess_rowSigma : MeasurableSpace RealHaarInput := borel RealHaarInput
local instance nativeObservationProcess_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩

theorem kernel_measurable (ell M : ℝ) (hell : 0 < ell) :
    Measurable (NativeHeatObservation.kernel ell M hell) :=
  (RealHaarIntegrand.kernel_measurable ell M hell).comp
    ((measurable_fst.div_const timeScale).prodMk measurable_snd)

theorem row_norm_sq_bound {ell M T r t : ℝ} (hell : 0 < ell) (f : EllipticField ell M)
    (ht : t < T) (hr : r ≤ t) (x : HeatCircle) :
    ‖row hell f T r x‖^2 ≤ M*(1+heatConstant*(T-t)^(-(1/2:ℝ))) := by
  let a := nativeFactorAnalysis f.1 ell M hell f.2.1 f.2.2 (circleHeat (T-r) x)
  have hre : ‖realInputPart a‖ ≤ ‖a‖ := lp.norm_mono (by norm_num : (2:ENNReal) ≠ 0)
    (fun q => by change ‖(a q).re‖ ≤ ‖a q‖; simpa only [Real.norm_eq_abs] using Complex.abs_re_le_norm (a q))
  have hB : ‖a‖^2 ≤ M*‖circleHeat (T-r) x‖^2 := by
    change ‖factorAnalysis f.1 ell M hell f.2.1 f.2.2 (CircleNormalization.push.symm (circleHeat (T-r) x))‖^2 ≤ _
    rw [factorAnalysis_norm_sq]
    have hb := (globalHaarColumn_bessel f.1 ell M hell f.2.1 f.2.2
      (CircleNormalization.push.symm (circleHeat (T-r) x))).2
    simpa only [LinearIsometryEquiv.norm_map] using hb
  have hM : 0 ≤ M := elliptic_upper_nonneg f.1 ell M hell f.2.2
  have hrt : 0 < T-r := lt_of_lt_of_le (sub_pos.mpr ht) (sub_le_sub_left hr T)
  have hpow := Real.rpow_le_rpow_of_nonpos (sub_pos.mpr ht) (sub_le_sub_left hr T)
    (by norm_num : -(1/2:ℝ) ≤ 0)
  calc
    ‖row hell f T r x‖^2 ≤ ‖a‖^2 := pow_le_pow_left₀ (norm_nonneg _) hre 2
    _ ≤ M*‖circleHeat (T-r) x‖^2 := hB
    _ ≤ M*(1+heatConstant*(T-t)^(-(1/2:ℝ))) := mul_le_mul_of_nonneg_left
      ((circleHeat_norm_sq_bound hrt x).trans
        (add_le_add le_rfl (mul_le_mul_of_nonneg_left hpow heatConstant_pos.le))) hM

variable {Ω : Type*} [MeasurableSpace Ω]

def integrand {ell M : ℝ} (hell : 0 < ell) (f : ℝ≥0 × Ω → EllipticField ell M)
    (T t : ℝ) (x : HeatCircle) (p : ℝ≥0 × Ω) : RealHaarInput :=
  columnFunctional (T-t) x (NativeHeatObservation.kernel ell M hell (t-(p.1:ℝ),f p))

theorem integrand_eq {ell M : ℝ} (hell : 0 < ell) (f : ℝ≥0 × Ω → EllipticField ell M)
    {T t : ℝ} (ht : t < T) (x : HeatCircle) (p : ℝ≥0 × Ω) :
    integrand hell f T t x p=if (p.1:ℝ) < t then row hell (f p) T (p.1:ℝ) x else 0 :=
  stopped_observed_kernel hell ht (f p) x

theorem integrand_predictable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›)
    {ell M : ℝ} (hell : 0 < ell) {f : ℝ≥0 × Ω → EllipticField ell M}
    (hf : StronglyMeasurable[𝓕.predictable] f) (T t : ℝ) (x : HeatCircle) :
    StronglyMeasurable[𝓕.predictable] (integrand hell f T t x) := by
  have hk := ((kernel_measurable ell M hell).comp
    (((measurable_const (a := t)).sub (PredictableClock.real_time_measurable 𝓕)).prodMk hf.measurable)).stronglyMeasurable
  exact (columnFunctional (T-t) x).continuous.comp_stronglyMeasurable hk

theorem integrand_norm_bound {ell M T t : ℝ} (hell : 0 < ell) (hM : 0 ≤ M)
    (f : ℝ≥0 × Ω → EllipticField ell M) (ht : t < T) (x : HeatCircle) (p : ℝ≥0 × Ω) :
    ‖integrand hell f T t x p‖ ≤ Real.sqrt (M*(1+heatConstant*(T-t)^(-(1/2:ℝ)))) := by
  have hC : 0 ≤ M*(1+heatConstant*(T-t)^(-(1/2:ℝ))) :=
    mul_nonneg hM (add_nonneg zero_le_one (mul_nonneg heatConstant_pos.le (Real.rpow_nonneg (sub_pos.mpr ht).le _)))
  rw [integrand_eq hell f ht x p]
  split_ifs with hp
  · have hb := row_norm_sq_bound hell (f p) ht hp.le x
    nlinarith [Real.sq_sqrt hC,Real.sqrt_nonneg (M*(1+heatConstant*(T-t)^(-(1/2:ℝ)))),norm_nonneg (row hell (f p) T (p.1:ℝ) x)]
  · simpa only [norm_zero] using Real.sqrt_nonneg (M*(1+heatConstant*(T-t)^(-(1/2:ℝ))))

theorem integrand_memLp (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›)
    (μ : Measure Ω) [IsProbabilityMeasure μ] (h : ℝ≥0)
    {ell M : ℝ} (hell : 0 < ell) (hM : 0 ≤ M)
    {f : ℝ≥0 × Ω → EllipticField ell M} (hf : StronglyMeasurable[𝓕.predictable] f)
    {T t : ℝ} (ht : t < T) (x : HeatCircle) :
    @MemLp _ _ 𝓕.predictable _ _ (integrand hell f T t x) 2
      ((energyMeasure μ h).trim (predictable_le_product 𝓕)) := by
  have : IsFiniteMeasure (energyMeasure μ h) := by dsimp [energyMeasure]; infer_instance
  exact MemLp.of_bound (integrand_predictable 𝓕 hell hf T t x).aestronglyMeasurable _
    (Filter.Eventually.of_forall (integrand_norm_bound hell hM f ht x))

def process (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›)
    (μ : Measure Ω) [IsProbabilityMeasure μ] (h : ℝ≥0)
    {ell M : ℝ} (hell : 0 < ell) (hM : 0 ≤ M)
    (f : ℝ≥0 × Ω → EllipticField ell M) (hf : StronglyMeasurable[𝓕.predictable] f)
    {T t : ℝ} (ht : t < T) (x : HeatCircle) : Process (E := RealHaarInput) 𝓕 μ h :=
  (integrand_memLp 𝓕 μ h hell hM hf ht x).toLp (integrand hell f T t x)

theorem process_ae (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›)
    (μ : Measure Ω) [IsProbabilityMeasure μ] (h : ℝ≥0)
    {ell M : ℝ} (hell : 0 < ell) (hM : 0 ≤ M)
    (f : ℝ≥0 × Ω → EllipticField ell M) (hf : StronglyMeasurable[𝓕.predictable] f)
    {T t : ℝ} (ht : t < T) (x : HeatCircle) :
    process 𝓕 μ h hell hM f hf ht x =ᵐ[energyMeasure μ h] integrand hell f T t x :=
  ae_eq_of_ae_eq_trim (integrand_memLp 𝓕 μ h hell hM hf ht x).coeFn_toLp

end SHE.NativeObservationProcess
