module

public import SHEStochastic.HilbertGaussianRecognition
public import SHEStochastic.ConditionalCharacteristic
public import Mathlib.Probability.Distributions.Gaussian.Real

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHEStochastic.HilbertGaussianLaw
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

variable {Ω C ι : Type*} [MeasurableSpace Ω] [Countable ι] [DecidableEq ι]
  [NormedAddCommGroup C] [InnerProductSpace ℝ C] [CompleteSpace C]
  [MeasurableSpace C] [BorelSpace C] [SecondCountableTopology C]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {H : ℝ≥0}

local notation "νt" => MathFin.ItoIntegralCLM.timeMeasure_T H
local notation "ν" => FiniteScalarIto.inputMeasure F μ H

/-- A predictable Hilbert row with deterministic time energy, supported
after `a`, has a Gaussian native integral independent of the entire
original sigma algebra at `a`. -/
theorem law_and_independent (P : FiniteScalarIto.Family F μ H ι) (e : HilbertBasis ι ℝ C)
    (a : ℝ≥0) (haH : a ≤ H) (u : Lp C 2 ν)
    (hu : ∀ᵐ p ∂ν, p.1 ≤ a → u p = 0) (q : ℝ≥0 → ℝ) (hq : Integrable q νt) (hq0 : ∀ r, 0 ≤ q r)
    (hqp : StronglyMeasurable[F.predictable] (fun p : ℝ≥0 × Ω ↦ q p.1))
    (hprofile : ∀ᵐ p ∂ν, ‖u p‖ ^ 2 = q p.1) :
    HasLaw (FiniteCylindricalIto.rawIntegral P.toCoordinates e u : Ω → ℝ)
      (gaussianReal 0 (∫ r, q r ∂νt).toNNReal) μ ∧
    Indep (MeasurableSpace.comap (FiniteCylindricalIto.rawIntegral P.toCoordinates e u : Ω → ℝ) (borel ℝ))
      (F a) μ := by
  letI : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
  let Z : Lp ℝ 2 μ := FiniteCylindricalIto.rawIntegral P.toCoordinates e u
  let Q : ℝ := ∫ r, q r ∂νt
  have hQ : 0 ≤ Q := integral_nonneg hq0
  apply ConditionalCharacteristic.law_and_independent (F a) (F.le a) (Lp.stronglyMeasurable Z).measurable
  intro x A hA
  let φ : Ω → ℂ := A.indicator (fun _ ↦ 1)
  have hφ : StronglyMeasurable[F a] φ := stronglyMeasurable_const.indicator hA
  have hφbound (ω : Ω) : ‖φ ω‖ ≤ 1 := by
    by_cases hω : ω ∈ A
    · simp [φ, Set.indicator_of_mem hω]
    · simp [φ, Set.indicator_of_notMem hω]
  have hh := HilbertGaussianRecognition.weighted_frequency_from_past P e a haH u hu q hq hq0 hqp
    hprofile φ hφ hφbound x
  change CharacteristicL2.weightedExpectation (A.indicator (fun _ ↦ (1 : ℂ))) (x • Z) = _ at hh
  rw [CharacteristicL2.weightedExpectation_indicator (F.le a _ hA)] at hh
  have hphase : (fun ω ↦ Complex.exp ((inner ℝ (Z ω) x : ℂ) * Complex.I)) =ᵐ[μ]
      (fun ω ↦ Complex.exp (((x • Z : Lp ℝ 2 μ) ω : ℂ) * Complex.I)) := by
    filter_upwards [Lp.coeFn_smul x Z] with ω hω
    apply congrArg (fun r : ℝ ↦ Complex.exp ((r : ℂ) * Complex.I))
    rw [Real.inner_apply, hω]
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  have hchar : charFun (gaussianReal 0 Q.toNNReal) x = (Real.exp (-(x ^ 2 * Q) / 2) : ℂ) := by
    rw [charFun_gaussianReal, Complex.ofReal_exp]
    congr 1
    have hQc : ((Q.toNNReal : ℝ) : ℂ) = (Q : ℂ) := congrArg ((↑) : ℝ → ℂ) (Real.coe_toNNReal Q hQ)
    rw [hQc]
    push_cast
    ring
  calc
    _ = CharacteristicL2.setExpectation A (x • Z) :=
      integral_congr_ae (hphase.filter_mono ae_restrict_le)
    _ = (Real.exp (-(x ^ 2 * Q) / 2) : ℂ) * ∫ ω, φ ω ∂μ := hh
    _ = μ.real A • charFun (gaussianReal 0 Q.toNNReal) x := by
      rw [hchar]
      dsimp only [φ]
      rw [integral_indicator (F.le a _ hA), setIntegral_const]
      simp only [Complex.real_smul, mul_one]
      ring

end SHEStochastic.HilbertGaussianLaw
