module

public import SHEStochastic.NativeStateDriverCoordinates
public import SHEStochastic.FourierNativeGeneratorDensity

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section

namespace SHEStochastic.JointFourierNativeGeneratorDensity
open MeasureTheory SHE SHE.PredictableL2 SHE.StoppedFourier AddCircle Filter
open GaussianItoTest GaussianTaylorAverage FiniteCovariancePullback FourierDiagonalFlow NativeFourierHeatCoordinate
open FiniteStateDriverCoordinates
open scoped ENNReal NNReal ContDiff

local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
local instance : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨by simp⟩

variable {Ω E V : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]
  {G : E → V} {C β : ℝ≥0} (hG : HolderWith C β G) (hβ : 0 < β) (hβ1 : β < 1)
  {s d : ℕ} (a : Fin s → ℂ →L[ℝ] ℝ) (n : Fin s → ℤ)
  {ι : Type*} [Countable ι] [DecidableEq ι]
  (e : HilbertBasis ι ℝ (Lp V 2 (haarAddCircle (T := 2 * Real.pi)))) (driver : Fin d → ι)

local instance : MeasurableSpace (Lp V 2 (haarAddCircle (T := 2 * Real.pi))) := borel _
local instance : BorelSpace (Lp V 2 (haarAddCircle (T := 2 * Real.pi))) := ⟨rfl⟩

def physicalRows (u : Lp E 2 (haarAddCircle (T := 2 * Real.pi))) :
    Fin (s + d) → Lp V 2 (haarAddCircle (T := 2 * Real.pi)) :=
  Fin.addCases (fun i ↦ StateNoiseCovariance.row haarAddCircle hβ hβ1.le hG (weight (a i) (n i)) u)
    (fun j ↦ e (driver j))

def density (f : State (s + d) → ℝ) (hf : ContDiff ℝ 2 f) (hs : HasCompactSupport f)
    (u : Lp E 2 (haarAddCircle (T := 2 * Real.pi))) (z : State (s + d)) : ℝ :=
  FourierCylinderGenerator.heatDrift f hf hs (frequencies (d := d) n) z +
    (1 / 2 : ℝ) * ∑ i : Fin (s + d), ∑ j : Fin (s + d),
      inner ℝ (physicalRows hG hβ hβ1 a n e driver u i) (physicalRows hG hβ hβ1 a n e driver u j) *
        GaussianTaylor.hessian f z (EuclideanSpace.basisFun (Fin (s + d)) ℝ i)
          (EuclideanSpace.basisFun (Fin (s + d)) ℝ j)

variable (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›)
  (U : ℝ≥0 × Ω → Lp E 2 (haarAddCircle (T := 2 * Real.pi)))
  (hU : StronglyMeasurable[F.predictable] U) (μ : Measure Ω) [IsProbabilityMeasure μ]
  (H : ℝ≥0) {R : ℝ} (hbound : ∀ᵐ p ∂energyMeasure μ H, ‖U p‖ ≤ R)

def growing : Fin (s + d) → Process (E := Lp V 2 (haarAddCircle (T := 2 * Real.pi))) F μ H :=
  NativeStateDriverCoordinates.rows e driver
    (fun i ↦ FourierHeatInput.growingInput F U hU hG hβ hβ1 μ H hbound (a i) (n i))

/-- The same diagonal cancellation applies to the enlarged state/driver
vector: the driver frequencies are zero, so their constant inputs remain
unchanged. This includes every mixed covariance entry. -/
theorem mapped_growing : ∀ᵐ p ∂energyMeasure μ H,
    mappedRow (clamped H (frequencies (d := d) n) p.1)
      (fun i ↦ growing hG hβ hβ1 a n e driver F U hU μ H hbound i p) =
        physicalRows hG hβ hβ1 a n e driver (U p) := by
  have hg := ae_all_iff.mpr (fun i ↦ ae_eq_of_ae_eq_trim
    (FourierHeatInput.growing_ae_trim F U hU hG hβ hβ1 μ H hbound (a i) (n i)))
  have hc := ae_all_iff.mpr (fun j : Fin d ↦ ae_eq_of_ae_eq_trim
    ((RotatedCylindricalCoordinates.constant_memLp F μ H (e (driver j))).coeFn_toLp))
  have ht : ∀ᵐ p ∂energyMeasure μ H, p.1 ≤ H :=
    Measure.quasiMeasurePreserving_fst.ae ((timeMeasure_ae_mem H).mono fun _ hs ↦ hs.2)
  filter_upwards [hg, hc, ht] with p hg hc ht
  have hcl : clamped H (frequencies (d := d) n) p.1 = raw (frequencies (d := d) n) p.1 :=
    congrArg (raw (frequencies (d := d) n)) (ClampedAbsoluteContinuity.of_mem ⟨p.1.property, ht⟩)
  funext j
  rw [hcl, FourierDecayCovariance.mapped_row_raw]
  refine Fin.addCases ?_ ?_ j
  · intro i
    simp only [growing, NativeStateDriverCoordinates.rows, physicalRows, frequencies, Fin.addCases_left]
    rw [hg i, smul_smul]
    have he : Real.exp (-(p.1 : ℝ) * (n i : ℝ) ^ 2) * FourierHeatInput.multiplier H (n i) p = 1 := by
      change Real.exp (-(p.1 : ℝ) * (n i : ℝ) ^ 2) *
        Real.exp (min (p.1 : ℝ) (H : ℝ) * (n i : ℝ) ^ 2) = 1
      rw [min_eq_left (show (p.1 : ℝ) ≤ H from ht), ← Real.exp_add]
      convert Real.exp_zero using 1 <;> ring
    rw [he, one_smul, FourierNoiseCovariance.row_eq]
  · intro j
    simp only [growing, NativeStateDriverCoordinates.rows, physicalRows, frequencies, Fin.addCases_right]
    have hj : RawCylindricalCoordinates.row F μ H (e : ι → Lp V 2 haarAddCircle) (driver j) p = e (driver j) := hc j
    rw [hj]
    simp

theorem action_cancel (f : State (s + d) → ℝ) (hf : ContDiff ℝ ∞ f) (hs : HasCompactSupport f)
    (Y : ℝ≥0 × Ω → State (s + d)) : ∀ᵐ p ∂energyMeasure μ H,
    covarianceAction (gram (fun i ↦ growing hG hβ hβ1 a n e driver F U hU μ H hbound i p))
      (GaussianTaylor.hessian (FourierDecayItoTest.value f H (frequencies (d := d) n) p.1) (Y p)) =
        ∑ i : Fin (s + d), ∑ j : Fin (s + d),
          inner ℝ (physicalRows hG hβ hβ1 a n e driver (U p) i) (physicalRows hG hβ hβ1 a n e driver (U p) j) *
            GaussianTaylor.hessian f (clamped H (frequencies (d := d) n) p.1 (Y p))
              (EuclideanSpace.basisFun (Fin (s + d)) ℝ i) (EuclideanSpace.basisFun (Fin (s + d)) ℝ j) := by
  filter_upwards [mapped_growing hG hβ hβ1 a n e driver F U hU μ H hbound] with p hp
  have hh := FiniteAffineDriftCancellation.action_hessian_comp (clamped H (frequencies (d := d) n) p.1)
    (fun i ↦ growing hG hβ hβ1 a n e driver F U hU μ H hbound i p)
    (SmoothLinearFamily.boundedSmooth_of_compact hf hs) (Y p)
  change covarianceAction _ (GaussianTaylor.hessian
    (fun w ↦ f (clamped H (frequencies (d := d) n) p.1 w)) (Y p)) = _
  rw [hh, hp]
  rfl

def nativeDensity (f : State (s + d) → ℝ) (hf : ContDiff ℝ 2 f) (hs : HasCompactSupport f)
    (Y : ℝ≥0 × Ω → State (s + d)) (r : ℝ) (sample : Ω) : ℝ :=
  FourierDecayItoTest.derivative f hf hs H (frequencies (d := d) n) r (Y (r.toNNReal, sample)) +
    (1 / 2 : ℝ) * covarianceAction
      (StandardFiniteIto.rowCovariance F μ H (growing hG hβ hβ1 a n e driver F U hU μ H hbound) sample r)
      (GaussianTaylor.hessian (FourierDecayItoTest.value f H (frequencies (d := d) n) r) (Y (r.toNNReal, sample)))

theorem pointwise (f : State (s + d) → ℝ) (hf : ContDiff ℝ 2 f) (hs : HasCompactSupport f)
    (hSmooth : ContDiff ℝ ∞ f) (Y : ℝ≥0 × Ω → State (s + d)) : ∀ᵐ p ∂energyMeasure μ H,
    nativeDensity hG hβ hβ1 a n e driver F U hU μ H hbound f hf hs Y p.1 p.2 =
      density hG hβ hβ1 a n e driver f hf hs (U p) (clamped H (frequencies (d := d) n) p.1 (Y p)) := by
  filter_upwards [action_cancel hG hβ hβ1 a n e driver F U hU μ H hbound f hSmooth hs Y] with p hp
  have hcov : StandardFiniteIto.rowCovariance F μ H
      (growing hG hβ hβ1 a n e driver F U hU μ H hbound) p.2 (p.1 : ℝ) =
      gram (fun i ↦ growing hG hβ hβ1 a n e driver F U hU μ H hbound i p) := by
    funext i j
    change inner ℝ
      (growing hG hβ hβ1 a n e driver F U hU μ H hbound i ((p.1 : ℝ).toNNReal, p.2))
      (growing hG hβ hβ1 a n e driver F U hU μ H hbound j ((p.1 : ℝ).toNNReal, p.2)) = _
    rw [Real.toNNReal_coe]
    rfl
  unfold nativeDensity
  rw [Real.toNNReal_coe, hcov, hp]
  rfl

theorem primitive (f : State (s + d) → ℝ) (hf : ContDiff ℝ 2 f) (hs : HasCompactSupport f)
    (hSmooth : ContDiff ℝ ∞ f) (Y : ℝ≥0 × Ω → State (s + d)) :
    ∀ᵐ sample ∂μ, ∀ T : ℝ≥0, T ≤ H →
      (∫ r in (0 : ℝ)..(T : ℝ), nativeDensity hG hβ hβ1 a n e driver F U hU μ H hbound f hf hs Y r sample) =
        ∫ r in (0 : ℝ)..(T : ℝ), density hG hβ hβ1 a n e driver f hf hs
          (U (r.toNNReal, sample)) (clamped H (frequencies (d := d) n) r (Y (r.toNNReal, sample))) := by
  apply AETimePrimitive.interval_integrals_eq μ H
  filter_upwards [pointwise hG hβ hβ1 a n e driver F U hU μ H hbound f hf hs hSmooth Y] with p hp
  simpa only [Real.toNNReal_coe] using hp

end SHEStochastic.JointFourierNativeGeneratorDensity
