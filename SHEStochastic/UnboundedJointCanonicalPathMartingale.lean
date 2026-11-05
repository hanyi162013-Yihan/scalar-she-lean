module

public import SHEStochastic.UnboundedJointCylinderIdentification
public import SHEStochastic.NativePathGeneratorFunctional

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 900000
noncomputable section

namespace SHEStochastic.UnboundedJointCanonicalPathMartingale
open MeasureTheory ProbabilityTheory SHE SHE.PredictableL2 SHE.StoppedFourier SHE.DyadicApproximation AddCircle Filter
open UnboundedNativeHeatEquation StoppedPathPasting UnboundedJointCylinderIdentification
open scoped ENNReal NNReal ContDiff

local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨by norm_num⟩
local instance : MeasurableSpace RealL2 := borel _
local instance : BorelSpace RealL2 := ⟨rfl⟩

variable {Ω V : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]
  {G : ℝ → V} {C β : ℝ≥0} (hG : HolderWith C β G) (hβ : 0 < β) (hβ1 : β < 1)
  {s d : ℕ} (f : GaussianItoTest.State (s + d) → ℝ) (a : Fin s → ℂ →L[ℝ] ℝ) (n : Fin s → ℤ)
  (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
  (W : ℝ≥0 → Ω → RealL2) (hW : StronglyMeasurable[F.predictable] (Function.uncurry W))
  {ι : Type*} [Countable ι] [DecidableEq ι]
  (P : FiniteScalarIto.Family F μ H ι)
  (e : HilbertBasis ι ℝ (Lp V 2 (haarAddCircle (T := 2 * Real.pi)))) (driver : Fin d → ι)

def path (hcW : ∀ sample, Continuous (fun t ↦ W t sample)) : Ω → Path (min H 1) (RealL2 × (ι → ℝ)) :=
  NativeContinuousPath.path (min H 1) (joint F μ H W P) (continuous_joint F μ H W P hcW)

def process (hcW : ∀ sample, Continuous (fun t ↦ W t sample))
    (hf : ContDiff ℝ 2 f) (hs : HasCompactSupport f) : ℝ≥0 → Ω → ℝ :=
  AdaptedCanonicalPathTests.martingale (min H 1) (path F μ H W P hcW)
    (JointFourierCylinderGenerator.test a n driver f hf hs)
    (JointFourierCylinderGenerator.value hG hβ hβ1.le a n (fun j ↦ e (driver j)) driver f hf hs)

include hW in
theorem adapted_path (hcW : ∀ sample, Continuous (fun t ↦ W t sample)) (t : Time (min H 1)) :
    Measurable[F (AdaptedCanonicalPathTests.toNN (min H 1) t)]
      (fun sample ↦ path F μ H W P hcW sample t) := by
  have ht : t.val.toNNReal = AdaptedCanonicalPathTests.toNN (min H 1) t :=
    NNReal.eq (Real.coe_toNNReal t.val t.property.1)
  change Measurable[F (AdaptedCanonicalPathTests.toNN (min H 1) t)]
    (joint F μ H W P t.val.toNNReal)
  rw [ht]
  exact joint_adapted F μ H W P hW _

include hW in
theorem measurable_path (hcW : ∀ sample, Continuous (fun t ↦ W t sample)) :
    Measurable (path F μ H W P hcW) := by
  apply ContinuousMap.measurable_iff_eval.mpr
  intro t
  exact (adapted_path F μ H W hW P hcW t).mono (F.le _) le_rfl

theorem process_eq_capped (hcW : ∀ sample, Continuous (fun t ↦ W t sample))
    (hf : ContDiff ℝ 2 f) (hs : HasCompactSupport f) :
    process hG hβ hβ1 f a n F μ H W P e driver hcW hf hs =
      stoppedProcess (canonical hG hβ hβ1 f a n F μ H W P e driver hf hs)
        (fun _ ↦ ((min H 1 : ℝ≥0) : WithTop ℝ≥0)) := by
  funext q sample
  rw [process, path, NativePathGeneratorFunctional.martingale_eq_capped]
  simp only [stoppedProcess, ← WithTop.coe_min, WithTop.untopA_eq_untop WithTop.coe_ne_top, WithTop.untop_coe]
  rfl

/-- The exact joint canonical path process used in weak convergence
and pasting is a native martingale after each actual L2 exit. -/
theorem stopped_random_martingale (ξ : Ω → RealL2) (hξ : StronglyMeasurable[F 0] ξ) (hInitial : W 0 =ᵐ[μ] ξ) (hH : 0 < H)
    (hcW : ∀ sample, Continuous (fun t ↦ W t sample))
    (hnull : NullCompleteFiltration.ContainsNullSets F μ)
    (hEquation : RandomEquation F μ H W hW hG hβ hβ1 P e ξ)
    (hf : ContDiff ℝ 2 f) (hSmooth : ContDiff ℝ ∞ f) (hs : HasCompactSupport f) (N : ℕ) :
    Martingale (stoppedProcess (process hG hβ hβ1 f a n F μ H W P e driver hcW hf hs) (exit W N)) F μ := by
  rw [process_eq_capped, stoppedProcess_stoppedProcess']
  have he : (fun sample ↦ min (exit W N sample) ((min H 1 : ℝ≥0) : WithTop ℝ≥0)) =
      (fun sample ↦ min ((min H 1 : ℝ≥0) : WithTop ℝ≥0) (exit W N sample)) :=
    funext fun _ ↦ min_comm _ _
  rw [he]
  exact UnboundedJointCylinderIdentification.stopped_random_martingale hG hβ hβ1 f a n F μ H W P e driver
    hW ξ hξ hInitial hH hcW hnull hEquation hf hSmooth hs N

/-- Deterministic-initial specialization. -/
theorem stopped_martingale (u₀ : RealL2) (hH : 0 < H)
    (hcW : ∀ sample, Continuous (fun t ↦ W t sample))
    (hnull : NullCompleteFiltration.ContainsNullSets F μ)
    (hEquation : Equation F μ H W hW hG hβ hβ1 P e u₀)
    (hf : ContDiff ℝ 2 f) (hSmooth : ContDiff ℝ ∞ f) (hs : HasCompactSupport f) (N : ℕ) :
    Martingale (stoppedProcess (process hG hβ hβ1 f a n F μ H W P e driver hcW hf hs) (exit W N)) F μ := by
  exact stopped_random_martingale hG hβ hβ1 f a n F μ H W hW P e driver (fun _ ↦ u₀) stronglyMeasurable_const
    (UnboundedNativeMildRecognition.initial F μ H W hW hG hβ hβ1 P e u₀ hH hcW hnull hEquation)
    hH hcW hnull hEquation hf hSmooth hs N

/-- For globally bounded coefficients the joint canonical expression
is an ordinary martingale on the whole initial horizon. Local L2 exits
are removed using the same reusable bounded-cylinder argument. -/
theorem bounded_random_martingale (ξ : Ω → RealL2) (hξ : StronglyMeasurable[F 0] ξ) (hInitial : W 0 =ᵐ[μ] ξ) (hH : 0 < H)
    (hcW : ∀ sample, Continuous (fun t ↦ W t sample))
    (hnull : NullCompleteFiltration.ContainsNullSets F μ)
    (hEquation : RandomEquation F μ H W hW hG hβ hβ1 P e ξ)
    (hf : ContDiff ℝ 2 f) (hSmooth : ContDiff ℝ ∞ f) (hs : HasCompactSupport f)
    (B : ℝ) (hB : 0 ≤ B) (hb : ∀ z, ‖G z‖ ≤ B) :
    Martingale (process hG hβ hβ1 f a n F μ H W P e driver hcW hf hs) F μ := by
  let test := JointFourierCylinderGenerator.test a n driver f hf hs
  let b := JointFourierCylinderGenerator.generator hG hβ hβ1.le B hB hb a n
    (fun j ↦ e (driver j)) driver f hf hs
  have heq : (b : RealL2 × (ι → ℝ) → ℝ) =
      JointFourierCylinderGenerator.value hG hβ hβ1.le a n (fun j ↦ e (driver j)) driver f hf hs :=
    funext fun q ↦ JointFourierCylinderGenerator.generator_value hG hβ hβ1.le B hB hb a n
      (fun j ↦ e (driver j)) driver f hf hs q
  have hSeq : IsLocalizingSequence F (fun N ↦ exit W N) μ :=
    { isStoppingTime := exit_stopping F W hW hcW
      mono := Eventually.of_forall (ContinuousNormExit.monotone (fun t sample ↦ physical W (t, sample)) (physical_continuous W hcW))
      tendsto_top := Eventually.of_forall (ContinuousNormExit.tendsto_top (fun t sample ↦ physical W (t, sample)) (physical_continuous W hcW)) }
  have hm := AdaptedCanonicalPathTests.martingale_of_stopped (min H 1) F (path F μ H W P hcW) μ
    test b (adapted_path F μ H W hW P hcW) (fun N ↦ exit W N) hSeq (fun N ↦ ?_)
  · rw [heq] at hm
    exact hm
  · rw [heq]
    exact stopped_random_martingale hG hβ hβ1 f a n F μ H W hW P e driver ξ hξ hInitial hH hcW hnull hEquation hf hSmooth hs _

/-- Deterministic-initial specialization. -/
theorem bounded_martingale (u₀ : RealL2) (hH : 0 < H)
    (hcW : ∀ sample, Continuous (fun t ↦ W t sample))
    (hnull : NullCompleteFiltration.ContainsNullSets F μ)
    (hEquation : Equation F μ H W hW hG hβ hβ1 P e u₀)
    (hf : ContDiff ℝ 2 f) (hSmooth : ContDiff ℝ ∞ f) (hs : HasCompactSupport f)
    (B : ℝ) (hB : 0 ≤ B) (hb : ∀ z, ‖G z‖ ≤ B) :
    Martingale (process hG hβ hβ1 f a n F μ H W P e driver hcW hf hs) F μ := by
  exact bounded_random_martingale hG hβ hβ1 f a n F μ H W hW P e driver (fun _ ↦ u₀) stronglyMeasurable_const
    (UnboundedNativeMildRecognition.initial F μ H W hW hG hβ hβ1 P e u₀ hH hcW hnull hEquation)
    hH hcW hnull hEquation hf hSmooth hs B hB hb

/-- The actual joint law of a bounded native solution with random L2
initial state satisfies every compact smooth Fourier/driver cylinder
identity. This is the form used by weak convergence and disintegration. -/
theorem bounded_random_identity (ξ : Ω → RealL2) (hξ : StronglyMeasurable[F 0] ξ)
    (hInitial : W 0 =ᵐ[μ] ξ) (hH : 0 < H)
    (hcW : ∀ sample, Continuous (fun t ↦ W t sample))
    (hnull : NullCompleteFiltration.ContainsNullSets F μ)
    (hEquation : RandomEquation F μ H W hW hG hβ hβ1 P e ξ)
    (hf : ContDiff ℝ 2 f) (hSmooth : ContDiff ℝ ∞ f) (hs : HasCompactSupport f)
    (B : ℝ) (hB : 0 ≤ B) (hb : ∀ z, ‖G z‖ ≤ B) :
    PastedCylinderMartingale.Identity (min H 1)
      (JointFourierCylinderGenerator.test a n driver f hf hs)
      (JointFourierCylinderGenerator.generator hG hβ hβ1.le B hB hb a n
        (fun j ↦ e (driver j)) driver f hf hs)
      (μ.map (path F μ H W P hcW)) := by
  apply AdaptedCanonicalPathTests.law_identity (min H 1) F (path F μ H W P hcW) μ
    _ _ (measurable_path F μ H W hW P hcW) (adapted_path F μ H W hW P hcW)
  rw [JointFourierCylinderGenerator.coe_generator]
  exact bounded_random_martingale hG hβ hβ1 f a n F μ H W hW P e driver ξ hξ hInitial
    hH hcW hnull hEquation hf hSmooth hs B hB hb

end SHEStochastic.UnboundedJointCanonicalPathMartingale
