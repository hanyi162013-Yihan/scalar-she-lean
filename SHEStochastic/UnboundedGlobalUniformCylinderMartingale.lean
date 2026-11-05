module

public import SHEStochastic.UnboundedGlobalCanonicalPathMartingale
public import SHEStochastic.UnboundedGlobalGeneratorAgreement
public import SHEStochastic.LocalMartingaleTransfer

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
noncomputable section

namespace SHEStochastic.UnboundedGlobalUniformCylinderMartingale
open MeasureTheory ProbabilityTheory SHE SHE.PredictableL2 SHE.StoppedFourier SHE.DyadicApproximation SHE.FiniteHaar AddCircle Filter
open UnboundedNativeHeatEquation UnboundedGlobalUniformRegularity StoppedPathPasting AdaptedCanonicalPathTests
open scoped ENNReal NNReal ContDiff

local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance : SecondCountableTopology CircleHeat.CircleL2 :=
  (_root_.fourierBasis (T := (1 : ℝ))).repr.toHomeomorph.secondCountableTopology
local instance : SecondCountableTopology RealL2 := realCircleIdentification.toHomeomorph.secondCountableTopology
local instance : MeasurableSpace RealL2 := borel _
local instance : BorelSpace RealL2 := ⟨rfl⟩
local instance (h : ℝ≥0) : Fact ((0 : ℝ) ≤ h) := ⟨h.property⟩

variable {Ω V : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]
  {G : ℝ → V} {C β : ℝ≥0} (hG : HolderWith C β G) (hβ : 0 < β) (hβ1 : β < 1)
  {d : ℕ} (f : GaussianItoTest.State d → ℝ) (a : Fin d → ℂ →L[ℝ] ℝ) (n : Fin d → ℤ)
  (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
  (W : ℝ≥0 → Ω → RealL2) (hW : StronglyMeasurable[F.predictable] (Function.uncurry W))
  {ι : Type*} [Countable ι] [DecidableEq ι]
  (P : FiniteScalarIto.Family F μ H ι)
  (e : HilbertBasis ι ℝ (Lp V 2 (haarAddCircle (T := 2 * Real.pi)))) (u₀ : RealL2)

def uniformProcess (hcW : ∀ sample, Continuous (fun t ↦ W t sample))
    (hf : ContDiff ℝ 2 f) (hs : HasCompactSupport f) (R : ℕ) : ℝ≥0 → Ω → ℝ :=
  stoppedProcess (AdaptedCanonicalPathTests.martingale H (NativeContinuousPath.path H W hcW)
    (FourierCylinderGenerator.test f hf hs a n) (FourierCylinderGenerator.generator f hf hs hG hβ hβ1.le R a n))
    (fun sample ↦ (toNN H (uniformExit H W hcW R sample) : WithTop ℝ≥0))

/-- The original native equation yields the local canonical martingale
for the bounded coefficient cutoff, stopped at the ACTUAL uniform exit.
The L2 localizing sequence and all generator replacements are proved. -/
theorem adapted_local (hH : 0 < H) (hcW : ∀ sample, Continuous (fun t ↦ W t sample))
    (hnull : NullCompleteFiltration.ContainsNullSets F μ)
    (hEquation : UnboundedGlobalNativeEquation.Equation F μ H W hW hG hβ hβ1 P e u₀)
    (M : ℝ) (hM : 0 ≤ M)
    (hu₀ : L2ExtendedUniformNorm.value (haarAddCircle (T := 1)) u₀ = ENNReal.ofReal M)
    (hf : ContDiff ℝ 2 f) (hSmooth : ContDiff ℝ ∞ f) (hs : HasCompactSupport f) (R : ℕ) :
    StronglyAdapted F (uniformProcess hG hβ hβ1 f a n H W hcW hf hs R) ∧
      Locally (fun X ↦ Martingale X F μ) F (uniformProcess hG hβ hβ1 f a n H W hcW hf hs R) μ := by
  let X := NativeContinuousPath.path H W hcW
  let test := FourierCylinderGenerator.test f hf hs a n
  let b := FourierCylinderGenerator.generator f hf hs hG hβ hβ1.le R a n
  let c := FourierCylinderGenerator.value f hG hβ hβ1.le a n
  let r := uniformExit H W hcW R
  let τ : Ω → WithTop ℝ≥0 := fun sample ↦ toNN H (r sample)
  let O := UnboundedGlobalCanonicalPathMartingale.process hG hβ hβ1 f a n H W hcW hf hs
  let B := AdaptedCanonicalPathTests.martingale H X test b
  have hτ : IsStoppingTime F τ :=
    UnboundedGlobalUniformRegularity.isStoppingTime F μ H W hW hG hβ hβ1 P e u₀ hH hcW hnull hEquation M hM hu₀ R
  have hBc := AdaptedCanonicalPathTests.martingale_continuous H X test b test.continuous b.continuous
  have hOc : ∀ sample, Continuous (O · sample) :=
    AdaptedCanonicalPathTests.martingale_continuous H X test c test.continuous
      (FourierCylinderGenerator.continuous_value f hf hG hβ hβ1.le a n)
  have hBa : StronglyAdapted F B := AdaptedCanonicalPathTests.martingale_adapted H F X test b
    (NativePathGeneratorFunctional.adapted H W hcW F hW)
  have heq : ∀ᵐ sample ∂μ, ∀ q, stoppedProcess B τ q sample = stoppedProcess O τ q sample := by
    filter_upwards [UnboundedGlobalGeneratorAgreement.canonical_value_agrees F μ H W hW hG hβ hβ1
      P e u₀ hH hcW hnull hEquation M hM hu₀ f hf hs a n R] with sample hh q
    change stoppedProcess (AdaptedCanonicalPathTests.martingale H X test b)
      (fun sample ↦ (toNN H (r sample) : WithTop ℝ≥0)) q sample =
      stoppedProcess (AdaptedCanonicalPathTests.martingale H X test c)
        (fun sample ↦ (toNN H (r sample) : WithTop ℝ≥0)) q sample
    rw [AdaptedCanonicalPathTests.stopped_martingale_native, AdaptedCanonicalPathTests.stopped_martingale_native]
    exact hh (clock H q)
  have hSeq : IsLocalizingSequence F (fun N ↦ exit W N) μ :=
    { isStoppingTime := exit_stopping F W hW hcW
      mono := Eventually.of_forall (ContinuousNormExit.monotone (fun t sample ↦ physical W (t, sample)) (physical_continuous W hcW))
      tendsto_top := Eventually.of_forall (ContinuousNormExit.tendsto_top (fun t sample ↦ physical W (t, sample)) (physical_continuous W hcW)) }
  exact LocalMartingaleTransfer.stopped F μ B O hBa hBc hOc
    (fun sample ↦ AdaptedCanonicalPathTests.martingale_zero H X test b sample) τ hτ heq
    (fun N ↦ exit W N) hSeq (fun N ↦ UnboundedGlobalCanonicalPathMartingale.stopped_martingale
      hG hβ hβ1 f a n F μ H W hW P e u₀ hH hcW hnull hEquation hf hSmooth hs N)

/-- Boundedness of the cutoff generator upgrades the derived local
martingale to an ordinary martingale at the uniform exit. -/
theorem martingale (hH : 0 < H) (hcW : ∀ sample, Continuous (fun t ↦ W t sample))
    (hnull : NullCompleteFiltration.ContainsNullSets F μ)
    (hEquation : UnboundedGlobalNativeEquation.Equation F μ H W hW hG hβ hβ1 P e u₀)
    (M : ℝ) (hM : 0 ≤ M)
    (hu₀ : L2ExtendedUniformNorm.value (haarAddCircle (T := 1)) u₀ = ENNReal.ofReal M)
    (hf : ContDiff ℝ 2 f) (hSmooth : ContDiff ℝ ∞ f) (hs : HasCompactSupport f) (R : ℕ) :
    Martingale (uniformProcess hG hβ hβ1 f a n H W hcW hf hs R) F μ := by
  have h := adapted_local hG hβ hβ1 f a n F μ H W hW P e u₀ hH hcW hnull hEquation M hM hu₀ hf hSmooth hs R
  let test := FourierCylinderGenerator.test f hf hs a n
  let b := FourierCylinderGenerator.generator f hf hs hG hβ hβ1.le R a n
  apply BoundedLocalMartingale.martingale μ F _ h.1 h.2 (2 * ‖test‖ + ‖b‖ * (H : ℝ≥0))
  intro q sample
  exact PastedGeneratorFunctional.norm_value_bound H test b
    (NativeContinuousPath.path H W hcW sample)
    (clock H (min (q : WithTop ℝ≥0)
      (toNN H (uniformExit H W hcW R sample) : WithTop ℝ≥0)).untopA)

end SHEStochastic.UnboundedGlobalUniformCylinderMartingale
