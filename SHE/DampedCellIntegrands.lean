module

public import SHE.DampedHeatKernel
public import SHE.HaarCellIntegrands

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section

namespace SHE.DampedCellIntegrands
open MeasureTheory Set Filter PredictableL2 ApproximationCells HaarKernelApproximation
open scoped NNReal ENNReal
local instance dampedCellIntegrands_pFinite : Fact ((2:ENNReal) ≠ ⊤) := ⟨by simp⟩
local instance dampedCellIntegrands_circleSigma : MeasurableSpace CircleHeat.CircleL2 := borel CircleHeat.CircleL2
local instance dampedCellIntegrands_circleBorel : BorelSpace CircleHeat.CircleL2 := ⟨rfl⟩
local instance dampedCellIntegrands_columnsSigma : MeasurableSpace Columns := borel Columns
local instance dampedCellIntegrands_columnsBorel : BorelSpace Columns := ⟨rfl⟩

variable {Ω : Type*} [MeasurableSpace Ω]

def kernel {Λ ell M : ℝ} (hell : 0 < ell) (f : ℝ≥0 × Ω → FiniteHaar.EllipticField ell M)
    (n k : ℕ) (p : ℝ≥0 × Ω) : Columns :=
  Real.exp (-Λ*((point n k:ℝ)-(p.1:ℝ))) • HaarCellIntegrands.kernel hell f n k p

theorem kernel_predictable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›)
    {Λ ell M : ℝ} (hell : 0 < ell) {f : ℝ≥0 × Ω → FiniteHaar.EllipticField ell M}
    (hf : StronglyMeasurable[𝓕.predictable] f) (n k : ℕ) :
    StronglyMeasurable[𝓕.predictable] (kernel (Λ := Λ) hell f n k) := by
  have he : @Measurable (ℝ≥0 × Ω) ℝ 𝓕.predictable _
      (fun p => Real.exp (-Λ*((point n k:ℝ)-(p.1:ℝ)))) :=
    Real.measurable_exp.comp (measurable_const.mul
      (measurable_const.sub (PredictableClock.real_time_measurable 𝓕)))
  exact (he.smul (HaarCellIntegrands.kernel_predictable 𝓕 hell hf n k).measurable).stronglyMeasurable

omit [MeasurableSpace Ω] in
theorem kernel_norm_le {Λ ell M : ℝ} (hΛ : 0 ≤ Λ) (hell : 0 < ell)
    (f : ℝ≥0 × Ω → FiniteHaar.EllipticField ell M) (n k : ℕ) (hk : k ≠ 0) (p : ℝ≥0 × Ω) :
    ‖kernel (Λ := Λ) hell f n k p‖ ≤ ‖HaarCellIntegrands.kernel hell f n k p‖ := by
  by_cases hs : p.1 ≤ point n (k-1)
  · have hage : 0 ≤ (point n k:ℝ)-(p.1:ℝ) := by
      have hs' : (p.1:ℝ) ≤ (point n (k-1):ℝ) := by exact_mod_cast hs
      linarith [HaarCellIntegrands.point_gap n k hk,(ApproximationClock.delta_pos n).le]
    have he : Real.exp (-Λ*((point n k:ℝ)-(p.1:ℝ))) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by nlinarith)
    rw [kernel,norm_smul,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
    exact (mul_le_mul_of_nonneg_right he (norm_nonneg _)).trans_eq (one_mul _)
  · simp only [kernel,HaarCellIntegrands.kernel,ite_eq_right hs,smul_zero,norm_zero,le_refl]

theorem kernel_memLp (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›)
    (μ : Measure Ω) [IsProbabilityMeasure μ] (h : ℝ≥0)
    {Λ ell M : ℝ} (hΛ : 0 ≤ Λ) (hell : 0 < ell) (hM : 0 ≤ M)
    {f : ℝ≥0 × Ω → FiniteHaar.EllipticField ell M} (hf : StronglyMeasurable[𝓕.predictable] f)
    (n k : ℕ) (hk : k ≠ 0) :
    @MemLp _ _ 𝓕.predictable _ _ (kernel (Λ := Λ) hell f n k) 2
      ((energyMeasure μ h).trim (predictable_le_product 𝓕)) :=
  (HaarCellIntegrands.kernel_memLp 𝓕 μ h hell hM hf n k hk).mono
    (kernel_predictable 𝓕 hell hf n k).aestronglyMeasurable
    (Filter.Eventually.of_forall (kernel_norm_le hΛ hell f n k hk))

def input (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›)
    (μ : Measure Ω) [IsProbabilityMeasure μ] (h : ℝ≥0)
    {Λ ell M : ℝ} (hΛ : 0 ≤ Λ) (hell : 0 < ell) (hM : 0 ≤ M)
    (f : ℝ≥0 × Ω → FiniteHaar.EllipticField ell M) (hf : StronglyMeasurable[𝓕.predictable] f)
    (n k : ℕ) : Process (E := Columns) 𝓕 μ h :=
  if hk : k ≠ 0 then (kernel_memLp 𝓕 μ h hΛ hell hM hf n k hk).toLp (kernel hell f n k) else 0

theorem input_ae (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›)
    (μ : Measure Ω) [IsProbabilityMeasure μ] (h : ℝ≥0)
    {Λ ell M : ℝ} (hΛ : 0 ≤ Λ) (hell : 0 < ell) (hM : 0 ≤ M)
    (f : ℝ≥0 × Ω → FiniteHaar.EllipticField ell M) (hf : StronglyMeasurable[𝓕.predictable] f)
    (n k : ℕ) (hk : k ≠ 0) :
    input 𝓕 μ h hΛ hell hM f hf n k =ᵐ[energyMeasure μ h] kernel (Λ := Λ) hell f n k := by
  simp only [input,dite_eq_left hk]
  exact ae_eq_of_ae_eq_trim (kernel_memLp 𝓕 μ h hΛ hell hM hf n k hk).coeFn_toLp

theorem input_stopped (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›)
    (μ : Measure Ω) [IsProbabilityMeasure μ] (h : ℝ≥0)
    {Λ ell M : ℝ} (hΛ : 0 ≤ Λ) (hell : 0 < ell) (hM : 0 ≤ M)
    (f : ℝ≥0 × Ω → FiniteHaar.EllipticField ell M) (hf : StronglyMeasurable[𝓕.predictable] f)
    (n k : ℕ) :
    ∀ᵐ p ∂energyMeasure μ h,point n (k-1) < p.1 → input 𝓕 μ h hΛ hell hM f hf n k p=0 := by
  by_cases hk : k ≠ 0
  · filter_upwards [input_ae 𝓕 μ h hΛ hell hM f hf n k hk] with p hp hs
    rw [hp,kernel,HaarCellIntegrands.kernel,ite_eq_right (not_le.mpr hs),smul_zero]
  · simp only [input,dite_eq_right hk]
    filter_upwards [ae_eq_of_ae_eq_trim (Lp.coeFn_zero Columns 2
      ((energyMeasure μ h).trim (predictable_le_product 𝓕)))] with p hp
    exact fun _ => hp

end SHE.DampedCellIntegrands
