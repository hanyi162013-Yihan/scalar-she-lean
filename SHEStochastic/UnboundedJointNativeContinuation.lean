module

public import SHEStochastic.UnboundedJointCanonicalPathMartingale
public import SHEStochastic.UnboundedNativeContinuation

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
noncomputable section

namespace SHEStochastic.UnboundedJointNativeContinuation
open MeasureTheory ProbabilityTheory SHE SHE.PredictableL2 SHE.StoppedFourier SHE.DyadicApproximation AddCircle Filter
open UnboundedNativeHeatEquation UnboundedNativeUniformRegularity StoppedPathPasting AdaptedCanonicalPathTests
open UnboundedJointCanonicalPathMartingale
open scoped ENNReal NNReal ContDiff

local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨by norm_num⟩
local instance : MeasurableSpace RealL2 := borel _
local instance : BorelSpace RealL2 := ⟨rfl⟩

variable {Ω V : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]
  (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
  (W : ℝ≥0 → Ω → RealL2) (hW : StronglyMeasurable[F.predictable] (Function.uncurry W))
  {G : ℝ → V} {C β : ℝ≥0} (hG : HolderWith C β G) (hβ : 0 < β) (hβ1 : β < 1)
  {ι : Type*} [Countable ι] [DecidableEq ι]
  (P : FiniteScalarIto.Family F μ H ι)
  (e : HilbertBasis ι ℝ (Lp V 2 (haarAddCircle (T := 2 * Real.pi)))) (u₀ : RealL2)
  {s d : ℕ} (f : GaussianItoTest.State (s + d) → ℝ) (a : Fin s → ℂ →L[ℝ] ℝ)
  (n : Fin s → ℤ) (driver : Fin d → ι)
  (hH : 0 < H) (hcW : ∀ sample, Continuous (fun t ↦ W t sample))
  (hnull : NullCompleteFiltration.ContainsNullSets F μ)
  (hEquation : Equation F μ H W hW hG hβ hβ1 P e u₀)
  (M : ℝ) (hM : 0 ≤ M)
  (hu₀ : L2ExtendedUniformNorm.value (haarAddCircle (T := 1)) u₀ = ENNReal.ofReal M)
  (hf : ContDiff ℝ 2 f) (hs : HasCompactSupport f)

include hH hnull hEquation hM hu₀ in
theorem generator_agrees (R : ℕ) : ∀ᵐ sample ∂μ, ∀ t : Time (min H 1),
    t < uniformExit H W hcW R sample →
      JointFourierCylinderGenerator.cutoff hG hβ hβ1.le a n (fun j ↦ e (driver j)) driver f hf hs R
        (path F μ H W P hcW sample t) =
      JointFourierCylinderGenerator.value hG hβ hβ1.le a n (fun j ↦ e (driver j)) driver f hf hs
        (path F μ H W P hcW sample t) := by
  filter_upwards [regularity F μ H W hW hG hβ hβ1 P e u₀ hH hcW hnull hEquation M hM hu₀]
    with sample hreg t ht
  let u := NativeContinuousPath.path (min H 1) W hcW sample t
  have hb := UniformCoefficientExit.before_bound (haarAddCircle (T := 1)) (min H 1) R
    (NativeContinuousPath.path (min H 1) W hcW sample) hreg.1 hreg.2 t ht
  have hp : L2ExtendedUniformNorm.value haarAddCircle (NativePhysicalState.push u) ≤ ENNReal.ofReal (R : ℝ) :=
    (NativePhysicalState.uniform_norm_push u).trans_le hb
  exact JointFourierCylinderGenerator.cutoff_agrees hG hβ hβ1.le a n (fun j ↦ e (driver j)) driver f hf hs R
    (path F μ H W P hcW sample t)
    ((L2ExtendedUniformNorm.le_ofReal_iff haarAddCircle (NativePhysicalState.push u) R (by positivity)).mp hp)

include hH hnull hEquation hM hu₀ in
/-- The original unbounded SPDE yields the stopped joint local
martingale for its bounded cutoff, including the actual noise history. -/
theorem adapted_local (hSmooth : ContDiff ℝ ∞ f) (R : ℕ) :
    StronglyAdapted F (stoppedProcess
      (AdaptedCanonicalPathTests.martingale (min H 1) (path F μ H W P hcW)
        (JointFourierCylinderGenerator.test a n driver f hf hs)
        (JointFourierCylinderGenerator.cutoff hG hβ hβ1.le a n (fun j ↦ e (driver j)) driver f hf hs R))
      (fun sample ↦ (toNN (min H 1) (uniformExit H W hcW R sample) : WithTop ℝ≥0))) ∧
    Locally (fun X ↦ Martingale X F μ) F (stoppedProcess
      (AdaptedCanonicalPathTests.martingale (min H 1) (path F μ H W P hcW)
        (JointFourierCylinderGenerator.test a n driver f hf hs)
        (JointFourierCylinderGenerator.cutoff hG hβ hβ1.le a n (fun j ↦ e (driver j)) driver f hf hs R))
      (fun sample ↦ (toNN (min H 1) (uniformExit H W hcW R sample) : WithTop ℝ≥0))) μ := by
  have hSeq : IsLocalizingSequence F (fun N ↦ exit W N) μ :=
    { isStoppingTime := exit_stopping F W hW hcW
      mono := Eventually.of_forall (ContinuousNormExit.monotone (fun t sample ↦ physical W (t, sample)) (physical_continuous W hcW))
      tendsto_top := Eventually.of_forall (ContinuousNormExit.tendsto_top (fun t sample ↦ physical W (t, sample)) (physical_continuous W hcW)) }
  exact AdaptedCanonicalPathTests.local_of_generator_agreement (min H 1) F (path F μ H W P hcW) μ
    (JointFourierCylinderGenerator.test a n driver f hf hs)
    (JointFourierCylinderGenerator.cutoff hG hβ hβ1.le a n (fun j ↦ e (driver j)) driver f hf hs R)
    (JointFourierCylinderGenerator.value hG hβ hβ1.le a n (fun j ↦ e (driver j)) driver f hf hs)
    (JointFourierCylinderGenerator.continuous_value hG hβ hβ1.le a n (fun j ↦ e (driver j)) driver f hf hs)
    (adapted_path F μ H W hW P hcW) (uniformExit H W hcW R)
    (UnboundedNativeUniformRegularity.isStoppingTime F μ H W hW hG hβ hβ1 P e u₀ hH hcW hnull hEquation M hM hu₀ R)
    (generator_agrees F μ H W hW hG hβ hβ1 P e u₀ f a n driver hH hcW hnull hEquation M hM hu₀ hf hs R)
    (fun N ↦ exit W N) hSeq
    (fun N ↦ UnboundedJointCanonicalPathMartingale.stopped_martingale hG hβ hβ1 f a n F μ H W hW P e driver
      u₀ hH hcW hnull hEquation hf hSmooth hs N)

include hH hnull hEquation hM hu₀ in
/-- Actual joint state/driver pasting preserves the bounded-cutoff
cylinder identity. Kernel assumptions are required only at reached
exit states; construction and native-SPDE recognition are separate. -/
theorem law_identity (hSmooth : ContDiff ℝ ∞ f) (R : ℕ)
    (κ : Kernel (RealL2 × (ι → ℝ)) (Path (min H 1) (RealL2 × (ι → ℝ)))) [IsMarkovKernel κ]
    (hinitial : ∀ᵐ sample ∂μ, ∀ᵐ y ∂κ
      (StoppedContinuationMeasure.state (min H 1) (path F μ H W P hcW) (uniformExit H W hcW R) sample),
      y (origin (min H 1)) =
        StoppedContinuationMeasure.state (min H 1) (path F μ H W P hcW) (uniformExit H W hcW R) sample)
    (hfuture : ∀ᵐ sample ∂μ, PastedCylinderMartingale.Identity (min H 1)
      (JointFourierCylinderGenerator.test a n driver f hf hs)
      (JointFourierCylinderGenerator.cutoff hG hβ hβ1.le a n (fun j ↦ e (driver j)) driver f hf hs R)
      (κ (StoppedContinuationMeasure.state (min H 1) (path F μ H W P hcW) (uniformExit H W hcW R) sample))) :
    PastedCylinderMartingale.Identity (min H 1)
      (JointFourierCylinderGenerator.test a n driver f hf hs)
      (JointFourierCylinderGenerator.cutoff hG hβ hβ1.le a n (fun j ↦ e (driver j)) driver f hf hs R)
      (StoppedContinuationMeasure.law (min H 1) (path F μ H W P hcW) (uniformExit H W hcW R)
        (measurable_path F μ H W hW P hcW) (UnboundedNativeContinuation.exit_measurable F H W hW hcW R) μ κ) := by
  exact AdaptedCanonicalPathTests.continuation_identity_of_local (min H 1) F (path F μ H W P hcW) μ
    (JointFourierCylinderGenerator.test a n driver f hf hs)
    (JointFourierCylinderGenerator.cutoff hG hβ hβ1.le a n (fun j ↦ e (driver j)) driver f hf hs R)
    (measurable_path F μ H W hW P hcW) (uniformExit H W hcW R)
    (UnboundedNativeContinuation.exit_measurable F H W hW hcW R) (adapted_path F μ H W hW P hcW)
    (UnboundedNativeUniformRegularity.isStoppingTime F μ H W hW hG hβ hβ1 P e u₀ hH hcW hnull hEquation M hM hu₀ R)
    (adapted_local F μ H W hW hG hβ hβ1 P e u₀ f a n driver hH hcW hnull hEquation M hM hu₀ hf hs hSmooth R).2
    κ hinitial hfuture

end SHEStochastic.UnboundedJointNativeContinuation
