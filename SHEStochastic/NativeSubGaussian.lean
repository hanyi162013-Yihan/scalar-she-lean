module

public import SHEStochastic.NativeBoundedExponential
public import SHEStochastic.SubGaussianFourthMoment
public import Mathlib.Probability.Moments.SubGaussian

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHEStochastic.NativeSubGaussian
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

variable {Ω C ι : Type*} [MeasurableSpace Ω] [Countable ι] [DecidableEq ι]
  [NormedAddCommGroup C] [InnerProductSpace ℝ C] [CompleteSpace C]
  [MeasurableSpace C] [BorelSpace C] [SecondCountableTopology C]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {H : ℝ≥0}
local notation "νin" => FiniteScalarIto.inputMeasure F μ H

/-- A deterministic bound on the actual time energy gives the standard
sub-Gaussian MGF bound for the native terminal integral. -/
theorem exponential_bound (P : FiniteScalarIto.Family F μ H ι) (e : HilbertBasis ι ℝ C)
    (u : Lp C 2 νin) (K : ℝ≥0) (hu : ∀ᵐ ω ∂μ, NativeEnergy.energy u ω ≤ K) (a : ℝ) :
    Integrable (fun ω ↦ Real.exp (a * FiniteCylindricalIto.rawIntegral P.toCoordinates e u ω)) μ ∧
      (∫ ω, Real.exp (a * FiniteCylindricalIto.rawIntegral P.toCoordinates e u ω) ∂μ) ≤
        Real.exp ((K : ℝ) * a ^ 2 / 2) := by
  obtain ⟨hLp, hmean, _⟩ := NativeBoundedExponential.bounded_energy P e a u K K.property hu
  have hi := (hLp.integrable (by norm_num)).const_mul (Real.exp ((K : ℝ) * a ^ 2 / 2))
  have hb : (fun ω ↦ Real.exp (a * FiniteCylindricalIto.rawIntegral P.toCoordinates e u ω)) ≤ᵐ[μ]
      (fun ω ↦ Real.exp ((K : ℝ) * a ^ 2 / 2) * NativeExponential.density P e a u ω) := by
    filter_upwards [hu] with ω hω
    rw [NativeExponential.density, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_left hω (sq_nonneg a)]
  have hm : AEStronglyMeasurable
      (fun ω ↦ Real.exp (a * FiniteCylindricalIto.rawIntegral P.toCoordinates e u ω)) μ :=
    (Real.continuous_exp.comp_stronglyMeasurable
      (stronglyMeasurable_const.mul (Lp.stronglyMeasurable _))).aestronglyMeasurable
  have hdom : ∀ᵐ ω ∂μ,
      ‖Real.exp (a * FiniteCylindricalIto.rawIntegral P.toCoordinates e u ω)‖ ≤
        Real.exp ((K : ℝ) * a ^ 2 / 2) * NativeExponential.density P e a u ω := by
    filter_upwards [hb] with ω hω
    simpa only [Real.norm_of_nonneg (Real.exp_pos _).le] using hω
  have hexp := hi.mono' hm hdom
  refine ⟨hexp, ?_⟩
  have hh := integral_mono_ae hexp hi hb
  simpa only [integral_const_mul, hmean, mul_one] using hh

theorem hasSubgaussianMGF (P : FiniteScalarIto.Family F μ H ι) (e : HilbertBasis ι ℝ C)
    (u : Lp C 2 νin) (K : ℝ≥0) (hu : ∀ᵐ ω ∂μ, NativeEnergy.energy u ω ≤ K) :
    HasSubgaussianMGF (fun ω ↦ FiniteCylindricalIto.rawIntegral P.toCoordinates e u ω) K μ where
  integrable_exp_mul a := (exponential_bound P e u K hu a).1
  mgf_le a := (exponential_bound P e u K hu a).2

/-- Fourth moments of bounded-energy native integrals scale quadratically
with the energy cap, as needed for quadratic-variation errors. -/
theorem fourth_moment_le (P : FiniteScalarIto.Family F μ H ι) (e : HilbertBasis ι ℝ C)
    (u : Lp C 2 νin) (K : ℝ≥0) (hu : ∀ᵐ ω ∂μ, NativeEnergy.energy u ω ≤ K) :
    (∫ ω, (FiniteCylindricalIto.rawIntegral P.toCoordinates e u ω) ^ 4 ∂μ) ≤
      48 * Real.exp (1 / 2 : ℝ) * (K : ℝ) ^ 2 :=
  SubGaussianFourthMoment.integral_fourth_le (hasSubgaussianMGF P e u K hu)

end SHEStochastic.NativeSubGaussian
