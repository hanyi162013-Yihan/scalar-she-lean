module

public import SHEStochastic.UnboundedGlobalCylinderIdentification
public import SHEStochastic.NativePathGeneratorFunctional
public import SHEStochastic.UnboundedGlobalUniformRegularity

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
noncomputable section

namespace SHEStochastic.UnboundedGlobalCanonicalPathMartingale
open MeasureTheory SHE SHE.PredictableL2 SHE.StoppedFourier SHE.DyadicApproximation SHE.FiniteHaar AddCircle Filter
open UnboundedNativeHeatEquation StoppedPathPasting
open scoped ENNReal NNReal ContDiff

local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance : SecondCountableTopology CircleHeat.CircleL2 :=
  (_root_.fourierBasis (T := (1 : ℝ))).repr.toHomeomorph.secondCountableTopology
local instance : SecondCountableTopology RealL2 := realCircleIdentification.toHomeomorph.secondCountableTopology
local instance : MeasurableSpace RealL2 := borel _
local instance : BorelSpace RealL2 := ⟨rfl⟩

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

def process (hcW : ∀ sample, Continuous (fun t ↦ W t sample))
    (hf : ContDiff ℝ 2 f) (hs : HasCompactSupport f) : ℝ≥0 → Ω → ℝ :=
  AdaptedCanonicalPathTests.martingale H (NativeContinuousPath.path H W hcW)
    (FourierCylinderGenerator.test f hf hs a n) (FourierCylinderGenerator.value f hG hβ hβ1.le a n)

/-- The EXACT compact-path canonical process used by the pasting
interface is a martingale at every L2 exit, derived from the native SPDE. -/
theorem stopped_martingale (hH : 0 < H) (hcW : ∀ sample, Continuous (fun t ↦ W t sample))
    (hnull : NullCompleteFiltration.ContainsNullSets F μ)
    (hEquation : UnboundedGlobalNativeEquation.Equation F μ H W hW hG hβ hβ1 P e u₀)
    (hf : ContDiff ℝ 2 f) (hSmooth : ContDiff ℝ ∞ f) (hs : HasCompactSupport f) (N : ℕ) :
    Martingale (stoppedProcess (process hG hβ hβ1 f a n H W hcW hf hs) (exit W N)) F μ := by
  let Q := UnboundedNativeCylinderIdentification.canonical hG hβ hβ1 f a n W u₀
  have heq : ∀ᵐ sample ∂μ, ∀ q : ℝ≥0,
      process hG hβ hβ1 f a n H W hcW hf hs q sample =
        stoppedProcess Q (fun _ ↦ ((H : ℝ≥0) : WithTop ℝ≥0)) q sample := by
    filter_upwards [(UnboundedNativeMildRecognition.initial F μ H W hW hG hβ hβ1 P e u₀ hH hcW hnull
      (UnboundedGlobalNativeEquation.to_local F μ H W hW hG hβ hβ1 P e (fun _ ↦ u₀) hEquation))]
      with sample hi q
    rw [process, NativePathGeneratorFunctional.martingale_eq_capped]
    simp only [stoppedProcess, ← WithTop.coe_min, WithTop.untopA_eq_untop WithTop.coe_ne_top, WithTop.untop_coe]
    rw [hi]
    rfl
  have hstop : stoppedProcess (stoppedProcess Q (fun _ ↦ ((H : ℝ≥0) : WithTop ℝ≥0))) (exit W N) =
      stoppedProcess Q (fun sample ↦ min ((H : ℝ≥0) : WithTop ℝ≥0) (exit W N sample)) := by
    rw [stoppedProcess_stoppedProcess']
    congr 1
    funext sample
    exact min_comm _ _
  have hsEq := stoppedProcess_congr (τ := exit W N) heq
  rw [hstop] at hsEq
  have hm := UnboundedGlobalCylinderIdentification.stopped_martingale hG hβ hβ1 f a n F μ H W hW P e u₀
    hH hcW hnull hEquation hf hSmooth hs N
  have ha : StronglyAdapted F (stoppedProcess (process hG hβ hβ1 f a n H W hcW hf hs) (exit W N)) := fun t ↦
    NullCompleteFiltration.stronglyMeasurable_congr F μ hnull t (hm.stronglyAdapted t)
      (hsEq.mono fun sample hh ↦ hh t)
  exact hm.congr ha (fun t ↦ hsEq.mono fun sample hh ↦ (hh t).symm)

end SHEStochastic.UnboundedGlobalCanonicalPathMartingale
