module

public import SHE.ApproximationCells
public import SHE.HaarKernelL2Approximation
public import SHE.PredictableClock

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section

namespace SHE.HaarCellIntegrands
open MeasureTheory Set PredictableL2 ApproximationClock ApproximationCells
  CircleHeat FiniteHaar HaarIntegrandEnergy HaarKernelApproximation
open scoped NNReal ENNReal
local instance haarCellIntegrands_periodPos : Fact (0 < (1:ℝ)) := ⟨zero_lt_one⟩
local instance haarCellIntegrands_pFinite : Fact ((2:ENNReal) ≠ ⊤) := ⟨by simp⟩
local instance haarCellIntegrands_circleSigma : MeasurableSpace CircleL2 := borel CircleL2
local instance haarCellIntegrands_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩
local instance haarCellIntegrands_columnsSigma : MeasurableSpace Columns := borel Columns
local instance haarCellIntegrands_columnsBorel : BorelSpace Columns := ⟨rfl⟩

variable {Ω : Type*} [MeasurableSpace Ω]

def kernel {ell M : ℝ} (hell : 0 < ell) (f : ℝ≥0 × Ω → EllipticField ell M)
    (n k : ℕ) (p : ℝ≥0 × Ω) : Columns :=
  if p.1 ≤ point n (k-1) then
    RealHaarIntegrand.kernel ell M hell ((point n k:ℝ)-(p.1:ℝ),f p) else 0

theorem point_gap (n k : ℕ) (hk : k ≠ 0) :
    (point n k:ℝ)-(point n (k-1):ℝ)=delta n := by
  change delta n*(k:ℝ)-delta n*((k-1:ℕ):ℝ)=delta n
  rw [Nat.cast_sub (by omega : 1 ≤ k)]
  simp only [Nat.cast_one]
  ring

theorem kernel_predictable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›)
    {ell M : ℝ} (hell : 0 < ell) {f : ℝ≥0 × Ω → EllipticField ell M}
    (hf : StronglyMeasurable[𝓕.predictable] f) (n k : ℕ) :
    StronglyMeasurable[𝓕.predictable] (kernel hell f n k) := by
  have hm := (RealHaarIntegrand.kernel_measurable ell M hell).comp
    (((measurable_const (a := (point n k:ℝ))).sub (PredictableClock.real_time_measurable 𝓕)).prodMk hf.measurable)
  exact (hm.ite (measurableSet_le (PredictableClock.time_measurable 𝓕)
    (measurable_const (a := point n (k-1))))
    measurable_const).stronglyMeasurable

omit [MeasurableSpace Ω] in
theorem kernel_norm_sq_bound {ell M : ℝ} (hell : 0 < ell) (hM : 0 ≤ M)
    (f : ℝ≥0 × Ω → EllipticField ell M) (n k : ℕ) (hk : k ≠ 0) (p : ℝ≥0 × Ω) :
    ‖kernel hell f n k p‖^2 ≤ M*(1+2*HeatTrace.fractionalGaussianIntegral 0*(delta n)^(-(1/2:ℝ))) := by
  have hG : 0 ≤ HeatTrace.fractionalGaussianIntegral 0 :=
    (HeatTrace.fractionalGaussianIntegral_pos (by norm_num : (0:ℝ) < 1/2)).le
  by_cases hs : p.1 ≤ point n (k-1)
  · have hage : delta n ≤ (point n k:ℝ)-(p.1:ℝ) := by
      have hs' : (p.1:ℝ) ≤ (point n (k-1):ℝ) := by exact_mod_cast hs
      linarith [point_gap n k hk]
    have hb := HaarHeatIntegrand.kernel_norm_sq_bound hell ((delta_pos n).trans_le hage) (f p)
    have hr := Real.rpow_le_rpow_of_nonpos (delta_pos n) hage (by norm_num : -(1/2:ℝ) ≤ 0)
    rw [kernel,ite_eq_left hs,RealHaarIntegrand.kernel_norm_sq]
    apply hb.trans
    apply mul_le_mul_of_nonneg_left _ hM
    linarith [mul_le_mul_of_nonneg_left hr (by positivity : 0 ≤ 2*HeatTrace.fractionalGaussianIntegral 0)]
  · simp only [kernel,ite_eq_right hs,norm_zero,zero_pow (by norm_num : (2:ℕ) ≠ 0)]
    exact mul_nonneg hM (add_nonneg zero_le_one
      (mul_nonneg (mul_nonneg (by norm_num) hG) (Real.rpow_nonneg (delta_pos n).le _)))

theorem kernel_memLp (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›)
    (μ : Measure Ω) [IsProbabilityMeasure μ] (h : ℝ≥0)
    {ell M : ℝ} (hell : 0 < ell) (hM : 0 ≤ M)
    {f : ℝ≥0 × Ω → EllipticField ell M} (hf : StronglyMeasurable[𝓕.predictable] f)
    (n k : ℕ) (hk : k ≠ 0) :
    @MemLp _ _ 𝓕.predictable _ _ (kernel hell f n k) 2
      ((energyMeasure μ h).trim (predictable_le_product 𝓕)) := by
  let C := M*(1+2*HeatTrace.fractionalGaussianIntegral 0*(delta n)^(-(1/2:ℝ)))
  have hC : 0 ≤ C := by
    have hG : 0 ≤ HeatTrace.fractionalGaussianIntegral 0 :=
      (HeatTrace.fractionalGaussianIntegral_pos (by norm_num : (0:ℝ) < 1/2)).le
    dsimp only [C]
    exact mul_nonneg hM (add_nonneg zero_le_one
      (mul_nonneg (mul_nonneg (by norm_num) hG) (Real.rpow_nonneg (delta_pos n).le _)))
  have hs := kernel_predictable 𝓕 hell hf n k
  have hb : ∀ p,‖kernel hell f n k p‖ ≤ Real.sqrt C := by
    intro p
    have he := kernel_norm_sq_bound hell hM f n k hk p
    have he' : ‖kernel hell f n k p‖^2 ≤ C := he
    nlinarith [Real.sq_sqrt hC,Real.sqrt_nonneg C,norm_nonneg (kernel hell f n k p)]
  have : IsFiniteMeasure (energyMeasure μ h) := by
    dsimp only [energyMeasure]
    infer_instance
  exact MemLp.of_bound hs.aestronglyMeasurable (Real.sqrt C) (Filter.Eventually.of_forall hb)

def process (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›)
    (μ : Measure Ω) [IsProbabilityMeasure μ] (h : ℝ≥0)
    {ell M : ℝ} (hell : 0 < ell) (hM : 0 ≤ M)
    (f : ℝ≥0 × Ω → EllipticField ell M) (hf : StronglyMeasurable[𝓕.predictable] f)
    (n k : ℕ) (hk : k ≠ 0) : Process (E := Columns) 𝓕 μ h :=
  (kernel_memLp 𝓕 μ h hell hM hf n k hk).toLp (kernel hell f n k)

theorem process_ae (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›)
    (μ : Measure Ω) [IsProbabilityMeasure μ] (h : ℝ≥0)
    {ell M : ℝ} (hell : 0 < ell) (hM : 0 ≤ M)
    (f : ℝ≥0 × Ω → EllipticField ell M) (hf : StronglyMeasurable[𝓕.predictable] f)
    (n k : ℕ) (hk : k ≠ 0) :
    process 𝓕 μ h hell hM f hf n k hk =ᵐ[energyMeasure μ h] kernel hell f n k :=
  ae_eq_of_ae_eq_trim (kernel_memLp 𝓕 μ h hell hM hf n k hk).coeFn_toLp

end SHE.HaarCellIntegrands
