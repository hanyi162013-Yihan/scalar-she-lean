module

public import SHEStochastic.FourierDecayItoTest
public import SHEStochastic.FourierNoiseCovariance
public import SHE.FiniteAffineDriftCancellation

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
noncomputable section

namespace SHEStochastic.FourierDecayCovariance
open MeasureTheory SHE SHE.PredictableL2 SHE.StoppedFourier AddCircle Filter
open GaussianItoTest GaussianTaylorAverage FiniteCovariancePullback FourierDiagonalFlow NativeFourierHeatCoordinate
open scoped ENNReal NNReal ContDiff

local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

variable {d : ℕ}

theorem mapped_row_raw {A : Type*} [AddCommGroup A] [Module ℝ A]
    (n : Fin d → ℤ) (t : ℝ) (R : Fin d → A) (j : Fin d) :
    mappedRow (raw n t) R j = Real.exp (-t * (n j : ℝ) ^ 2) • R j := by
  classical
  unfold mappedRow coefficient
  rw [Finset.sum_eq_single j]
  · rw [raw_basis, PiLp.smul_apply]
    simp [EuclideanSpace.basisFun_apply, PiLp.single_apply]
  · intro i _ hij
    rw [raw_basis, PiLp.smul_apply]
    simp [EuclideanSpace.basisFun_apply, PiLp.single_apply, hij, Ne.symm hij]
  · simp

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
  (hbound : ∀ᵐ z ∂energyMeasure μ H, ‖U z‖ ≤ R)
  (a : Fin d → ℂ →L[ℝ] ℝ) (n : Fin d → ℤ)

/-- The heat-decay observation map cancels the integrating factor in
all actual Fourier noise rows on their original integration horizon. -/
theorem mapped_growing : ∀ᵐ p ∂energyMeasure μ H,
    mappedRow (clamped H n p.1)
      (fun i ↦ FourierHeatInput.growingInput F U hU hG hβ hβ1 μ H hbound (a i) (n i) p) =
      (fun i ↦ FourierHeatRowAverage.row F U hU hG hβ hβ1 (a i) (n i) p) := by
  have hg := ae_all_iff.mpr (fun i ↦ ae_eq_of_ae_eq_trim
    (FourierHeatInput.growing_ae_trim F U hU hG hβ hβ1 μ H hbound (a i) (n i)))
  have ht : ∀ᵐ p ∂energyMeasure μ H, p.1 ≤ H :=
    Measure.quasiMeasurePreserving_fst.ae ((timeMeasure_ae_mem H).mono fun _ hs ↦ hs.2)
  filter_upwards [hg, ht] with p hg ht
  have hcl : clamped H n p.1 = raw n p.1 := congrArg (raw n)
    (ClampedAbsoluteContinuity.of_mem ⟨p.1.property, ht⟩)
  funext j
  rw [hcl, mapped_row_raw, hg j, smul_smul]
  have he : Real.exp (-(p.1 : ℝ) * (n j : ℝ) ^ 2) * FourierHeatInput.multiplier H (n j) p = 1 := by
    change Real.exp (-(p.1 : ℝ) * (n j : ℝ) ^ 2) *
      Real.exp (min (p.1 : ℝ) (H : ℝ) * (n j : ℝ) ^ 2) = 1
    rw [min_eq_left (show (p.1 : ℝ) ≤ H from ht), ← Real.exp_add]
    convert Real.exp_zero using 1 <;> ring
  rw [he, one_smul]

/-- The original finite covariance/Hessian pullback identity gives
exact cancellation, including all mixed Fourier covariance entries. -/
theorem action_cancel (f : State d → ℝ) (hf : ContDiff ℝ ∞ f) (hs : HasCompactSupport f)
    (Y : ℝ≥0 × Ω → State d) :
    ∀ᵐ p ∂energyMeasure μ H,
      covarianceAction
        (gram (fun i ↦ FourierHeatInput.growingInput F U hU hG hβ hβ1 μ H hbound (a i) (n i) p))
        (GaussianTaylor.hessian (FourierDecayItoTest.value f H n p.1) (Y p)) =
      ∑ i : Fin d, ∑ j : Fin d,
        StateNoiseCovariance.value haarAddCircle hβ hβ1.le hG hG (weight (a i) (n i)) (weight (a j) (n j)) (U p) *
          GaussianTaylor.hessian f (clamped H n p.1 (Y p))
            (EuclideanSpace.basisFun (Fin d) ℝ i) (EuclideanSpace.basisFun (Fin d) ℝ j) := by
  have hb := SmoothLinearFamily.boundedSmooth_of_compact hf hs
  filter_upwards [mapped_growing F U hU hG hβ hβ1 μ H hbound a n] with p hp
  have hh := FiniteAffineDriftCancellation.action_hessian_comp (clamped H n p.1)
    (fun i ↦ FourierHeatInput.growingInput F U hU hG hβ hβ1 μ H hbound (a i) (n i) p) hb (Y p)
  change covarianceAction _ (GaussianTaylor.hessian (fun w ↦ f (clamped H n p.1 w)) (Y p)) = _
  rw [hh, hp]
  unfold covarianceAction gram
  simp_rw [FourierNoiseCovariance.row_covariance]

end SHEStochastic.FourierDecayCovariance
