module

public import SHEStochastic.UnboundedUniformCylinderMartingale

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
noncomputable section

namespace SHEStochastic.UnboundedNativeContinuation
open MeasureTheory ProbabilityTheory SHE SHE.PredictableL2 SHE.StoppedFourier SHE.DyadicApproximation SHE.FiniteHaar AddCircle
open UnboundedNativeHeatEquation UnboundedNativeUniformRegularity StoppedPathPasting AdaptedCanonicalPathTests
open scoped ENNReal NNReal ContDiff

local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance : SecondCountableTopology CircleHeat.CircleL2 :=
  (_root_.fourierBasis (T := (1 : ℝ))).repr.toHomeomorph.secondCountableTopology
local instance : SecondCountableTopology RealL2 := realCircleIdentification.toHomeomorph.secondCountableTopology
local instance : MeasurableSpace RealL2 := borel _
local instance : BorelSpace RealL2 := ⟨rfl⟩
local instance (h : ℝ≥0) : Fact ((0 : ℝ) ≤ h) := ⟨h.property⟩

variable {Ω : Type*} [MeasurableSpace Ω]
  (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (H : ℝ≥0)
  (W : ℝ≥0 → Ω → RealL2) (hW : StronglyMeasurable[F.predictable] (Function.uncurry W))

include hW in
theorem path_measurable (hcW : ∀ sample, Continuous (fun t ↦ W t sample)) :
    Measurable (NativeContinuousPath.path (min H 1) W hcW) :=
  NativeContinuousPath.measurable_path (min H 1) W hcW ((hW.mono (predictable_le_product F)).measurable)

include hW in
theorem exit_measurable (hcW : ∀ sample, Continuous (fun t ↦ W t sample)) (R : ℕ) :
    Measurable (uniformExit H W hcW R) :=
  (UniformCoefficientExit.measurable_exit (haarAddCircle (T := 1)) (min H 1) R).comp
    (path_measurable F H W hW hcW)

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]
  {G : ℝ → V} {C β : ℝ≥0} (hG : HolderWith C β G) (hβ : 0 < β) (hβ1 : β < 1)
  (μ : Measure Ω) [IsProbabilityMeasure μ]
  {ι : Type*} [Countable ι] [DecidableEq ι]
  (P : FiniteScalarIto.Family F μ H ι)
  (e : HilbertBasis ι ℝ (Lp V 2 (haarAddCircle (T := 2 * Real.pi)))) (u₀ : RealL2)
  {d : ℕ} (f : GaussianItoTest.State d → ℝ) (a : Fin d → ℂ →L[ℝ] ℝ) (n : Fin d → ℤ)

/-- Starting from the actual unbounded native SPDE, attach a bounded
continuation at its actual uniform exit. The resulting state law obeys
the bounded-cutoff canonical Fourier cylinder identity. The Borel
continuation kernel is required to have the right initial state and
future identities only at actually reached exit states; their SPDE existence/recognition remains separate. -/
theorem law_identity (hH : 0 < H) (hcW : ∀ sample, Continuous (fun t ↦ W t sample))
    (hnull : NullCompleteFiltration.ContainsNullSets F μ)
    (hEquation : Equation F μ H W hW hG hβ hβ1 P e u₀)
    (M : ℝ) (hM : 0 ≤ M)
    (hu₀ : L2ExtendedUniformNorm.value (haarAddCircle (T := 1)) u₀ = ENNReal.ofReal M)
    (hf : ContDiff ℝ 2 f) (hSmooth : ContDiff ℝ ∞ f) (hs : HasCompactSupport f) (R : ℕ)
    (κ : Kernel RealL2 (Path (min H 1) RealL2)) [IsMarkovKernel κ]
    (hinitial : ∀ᵐ sample ∂μ,
      ∀ᵐ y ∂κ ((NativeContinuousPath.path (min H 1) W hcW sample) (uniformExit H W hcW R sample)),
        y (origin (min H 1)) =
          (NativeContinuousPath.path (min H 1) W hcW sample) (uniformExit H W hcW R sample))
    (hfuture : ∀ᵐ sample ∂μ, PastedCylinderMartingale.Identity (min H 1)
      (FourierCylinderGenerator.test f hf hs a n) (FourierCylinderGenerator.generator f hf hs hG hβ hβ1.le R a n)
        (κ ((NativeContinuousPath.path (min H 1) W hcW sample) (uniformExit H W hcW R sample)))) :
    PastedCylinderMartingale.Identity (min H 1)
      (FourierCylinderGenerator.test f hf hs a n) (FourierCylinderGenerator.generator f hf hs hG hβ hβ1.le R a n)
      (StoppedContinuationMeasure.law (min H 1) (NativeContinuousPath.path (min H 1) W hcW)
        (uniformExit H W hcW R) (path_measurable F H W hW hcW) (exit_measurable F H W hW hcW R) μ κ) := by
  apply AdaptedCanonicalPathTests.continuation_identity_of_local (min H 1) F
    (NativeContinuousPath.path (min H 1) W hcW) μ
    (FourierCylinderGenerator.test f hf hs a n) (FourierCylinderGenerator.generator f hf hs hG hβ hβ1.le R a n)
    (path_measurable F H W hW hcW) (uniformExit H W hcW R) (exit_measurable F H W hW hcW R)
    (NativePathGeneratorFunctional.adapted (min H 1) W hcW F hW)
    (UnboundedNativeUniformRegularity.isStoppingTime F μ H W hW hG hβ hβ1 P e u₀ hH hcW hnull hEquation M hM hu₀ R)
    (UnboundedUniformCylinderMartingale.adapted_local hG hβ hβ1 f a n F μ H W hW P e u₀
      hH hcW hnull hEquation M hM hu₀ hf hSmooth hs R).2 κ hinitial hfuture

end SHEStochastic.UnboundedNativeContinuation
