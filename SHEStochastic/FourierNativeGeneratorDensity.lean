module

public import SHEStochastic.FourierDecayCovariance
public import SHEStochastic.AETimePrimitive

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
noncomputable section

namespace SHEStochastic.FourierNativeGeneratorDensity
open MeasureTheory SHE SHE.PredictableL2 SHE.StoppedFourier AddCircle Filter
open GaussianItoTest GaussianTaylorAverage FourierDiagonalFlow NativeFourierHeatCoordinate
open scoped ENNReal NNReal ContDiff

local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

variable {Ω E V : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]
  (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›)
  (U : ℝ≥0 × Ω → Lp E 2 (haarAddCircle (T := 2 * Real.pi)))
  (hU : StronglyMeasurable[F.predictable] U)
  {G : E → V} {C β : ℝ≥0} (hG : HolderWith C β G) (hβ : 0 < β) (hβ1 : β < 1)
  (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0) {R : ℝ}
  (hbound : ∀ᵐ p ∂energyMeasure μ H, ‖U p‖ ≤ R)
  {d : ℕ} (a : Fin d → ℂ →L[ℝ] ℝ) (n : Fin d → ℤ)
  (f : State d → ℝ) (hf : ContDiff ℝ 2 f) (hs : HasCompactSupport f)

def density (u : Lp E 2 (haarAddCircle (T := 2 * Real.pi))) (z : State d) : ℝ :=
  FourierCylinderGenerator.heatDrift f hf hs n z + (1 / 2 : ℝ) * ∑ i : Fin d, ∑ j : Fin d,
    StateNoiseCovariance.value haarAddCircle hβ hβ1.le hG hG (weight (a i) (n i)) (weight (a j) (n j)) u *
      GaussianTaylor.hessian f z (EuclideanSpace.basisFun (Fin d) ℝ i) (EuclideanSpace.basisFun (Fin d) ℝ j)

def nativeDensity (Y : ℝ≥0 × Ω → State d) (r : ℝ) (sample : Ω) : ℝ :=
  FourierDecayItoTest.derivative f hf hs H n r (Y (r.toNNReal, sample)) + (1 / 2 : ℝ) *
    covarianceAction (StandardFiniteIto.rowCovariance F μ H
      (fun i ↦ FourierHeatInput.growingInput F U hU hG hβ hβ1 μ H hbound (a i) (n i)) sample r)
      (GaussianTaylor.hessian (FourierDecayItoTest.value f H n r) (Y (r.toNNReal, sample)))

/-- The native finite Ito drift is exactly the physical generator
applied to its decayed finite state. All exponential weights cancel in
the proved mixed covariance pullback. -/
theorem pointwise (hSmooth : ContDiff ℝ ∞ f) (Y : ℝ≥0 × Ω → State d) :
    ∀ᵐ p ∂energyMeasure μ H,
      nativeDensity F U hU hG hβ hβ1 μ H hbound a n f hf hs Y p.1 p.2 =
        density hG hβ hβ1 a n f hf hs (U p) (clamped H n p.1 (Y p)) := by
  filter_upwards [FourierDecayCovariance.action_cancel F U hU hG hβ hβ1 μ H hbound a n f hSmooth hs Y] with p hp
  have hcov : StandardFiniteIto.rowCovariance F μ H
      (fun i ↦ FourierHeatInput.growingInput F U hU hG hβ hβ1 μ H hbound (a i) (n i)) p.2 (p.1 : ℝ) =
      FiniteCovariancePullback.gram
        (fun i ↦ FourierHeatInput.growingInput F U hU hG hβ hβ1 μ H hbound (a i) (n i) p) := by
    funext i j
    change inner ℝ
      (FourierHeatInput.growingInput F U hU hG hβ hβ1 μ H hbound (a i) (n i) ((p.1 : ℝ).toNNReal, p.2))
      (FourierHeatInput.growingInput F U hU hG hβ hβ1 μ H hbound (a j) (n j) ((p.1 : ℝ).toNNReal, p.2)) = _
    rw [Real.toNNReal_coe]
    rfl
  unfold nativeDensity
  rw [Real.toNNReal_coe, hcov, hp]
  rfl

/-- Equality holds for all drift primitives on one common event, so
later evaluation at a random stopping time is legitimate. -/
theorem primitive (hSmooth : ContDiff ℝ ∞ f) (Y : ℝ≥0 × Ω → State d) :
    ∀ᵐ sample ∂μ, ∀ T : ℝ≥0, T ≤ H →
      (∫ r in (0 : ℝ)..(T : ℝ), nativeDensity F U hU hG hβ hβ1 μ H hbound a n f hf hs Y r sample) =
      ∫ r in (0 : ℝ)..(T : ℝ), density hG hβ hβ1 a n f hf hs
        (U (r.toNNReal, sample)) (clamped H n r (Y (r.toNNReal, sample))) := by
  apply AETimePrimitive.interval_integrals_eq μ H
  filter_upwards [pointwise F U hU hG hβ hβ1 μ H hbound a n f hf hs hSmooth Y] with p hp
  simpa only [Real.toNNReal_coe] using hp

end SHEStochastic.FourierNativeGeneratorDensity
