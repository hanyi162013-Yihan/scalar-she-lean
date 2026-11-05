module

public import SHEStochastic.UnboundedGlobalFiniteFourier
public import SHEStochastic.UnboundedNativeCylinderIdentification

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
noncomputable section

namespace SHEStochastic.UnboundedGlobalCylinderIdentification
open MeasureTheory SHE SHE.PredictableL2 SHE.StoppedFourier SHE.DyadicApproximation AddCircle Filter
open UnboundedNativeHeatEquation UnboundedNativeCylinderIdentification
open scoped ENNReal NNReal ContDiff

local instance : Fact (0<2*Real.pi) := ⟨by positivity⟩
local instance : Fact (0<(1:ℝ)) := ⟨zero_lt_one⟩

variable {Ω V : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]
  {G : ℝ → V} {C β : ℝ≥0} (hG : HolderWith C β G) (hβ : 0<β) (hβ1 : β<1)
  {d : ℕ} (f : GaussianItoTest.State d → ℝ) (a : Fin d → ℂ →L[ℝ] ℝ) (n : Fin d → ℤ)
  (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
  (W : ℝ≥0 → Ω → RealL2) (hW : StronglyMeasurable[F.predictable] (Function.uncurry W))
  {ι : Type*} [Countable ι] [DecidableEq ι] (P : FiniteScalarIto.Family F μ H ι)
  (e : HilbertBasis ι ℝ (Lp V 2 (haarAddCircle (T:=2*Real.pi)))) (u₀ : RealL2)

/-- Global canonical cylinder martingale recognition reuses the same
proved finite-Itô identification as the original short-interval proof. -/
theorem exists_martingale (hH : 0<H) (hcW : ∀ sample, Continuous (fun t ↦ W t sample))
    (hnull : NullCompleteFiltration.ContainsNullSets F μ)
    (hEquation : UnboundedGlobalNativeEquation.Equation F μ H W hW hG hβ hβ1 P e u₀)
    (hf : ContDiff ℝ 2 f) (hSmooth : ContDiff ℝ ∞ f) (hs : HasCompactSupport f) (N : ℕ) :
    ∃ M : ℝ≥0 → Ω → ℝ, (∀ sample, Continuous (M · sample)) ∧ StronglyAdapted F M ∧
      StronglyMeasurable[F.predictable] (Function.uncurry M) ∧ Martingale M F μ ∧
      ∀ T : ℝ≥0, T≤H → ∀ᵐ sample ∂μ, (T:WithTop ℝ≥0)≤exit W N sample →
        canonical hG hβ hβ1 f a n W u₀ T sample=M T sample := by
  have hi := UnboundedNativeMildRecognition.initial F μ H W hW hG hβ hβ1 P e u₀ hH hcW hnull
    (UnboundedGlobalNativeEquation.to_local F μ H W hW hG hβ hβ1 P e (fun _ ↦ u₀) hEquation)
  obtain ⟨Y,hY,hcY,hYr,hClosed⟩ := UnboundedGlobalFiniteFourier.exists_random_version
    F μ H W hW hG hβ hβ1 P e (fun _ ↦ u₀) stronglyMeasurable_const hi hH hcW hnull hEquation N a n
  exact UnboundedNativeCylinderIdentification.exists_martingale_of_closed hG hβ hβ1 f a n
    F μ H W hW P e u₀ hcW hnull N H le_rfl hf hSmooth hs Y hY hcY hYr hClosed hi

/-- The actual canonical cylinder expression, stopped at the native
L2 exit and terminal time, is a martingale on every finite horizon. -/
theorem stopped_martingale (hH : 0<H) (hcW : ∀ sample, Continuous (fun t ↦ W t sample))
    (hnull : NullCompleteFiltration.ContainsNullSets F μ)
    (hEquation : UnboundedGlobalNativeEquation.Equation F μ H W hW hG hβ hβ1 P e u₀)
    (hf : ContDiff ℝ 2 f) (hSmooth : ContDiff ℝ ∞ f) (hs : HasCompactSupport f) (N : ℕ) :
    Martingale (stoppedProcess (canonical hG hβ hβ1 f a n W u₀)
      (fun sample ↦ min (H:WithTop ℝ≥0) (exit W N sample))) F μ := by
  obtain ⟨M,hcM,_,_,hmM,hr⟩ := exists_martingale hG hβ hβ1 f a n F μ H W hW P e u₀
    hH hcW hnull hEquation hf hSmooth hs N
  have hzero : canonical hG hβ hβ1 f a n W u₀ 0=ᵐ[μ] M 0 :=
    (hr 0 zero_le).mono fun sample hh ↦ hh
      (by exact_mod_cast (show (⊥:WithTop ℝ≥0)≤exit W N sample from bot_le))
  have he (T : ℝ≥0) (ht : T<H) : ∀ᵐ sample ∂μ, (T:WithTop ℝ≥0)<exit W N sample →
      canonical hG hβ hβ1 f a n W u₀ T sample=M T sample :=
    (hr T ht.le).mono fun _ hh hb ↦ hh hb.le
  have heq := ContinuousEqualityBeforeExit.stopped_eq_horizon μ
    (canonical hG hβ hβ1 f a n W u₀) M H (exit W N)
    (Eventually.of_forall (continuous_canonical hG hβ hβ1 f a n hf W hcW u₀))
    (Eventually.of_forall hcM) hzero he
  have hτ : IsStoppingTime F (fun sample ↦ min (H:WithTop ℝ≥0) (exit W N sample)) :=
    (isStoppingTime_const F H).min (exit_stopping F W hW hcW N)
  have hm := hmM.stoppedProcess (fun sample t ↦ (hcM sample).continuousAt.continuousWithinAt) hτ
  have ha : StronglyAdapted F (stoppedProcess (canonical hG hβ hβ1 f a n W u₀)
      (fun sample ↦ min (H:WithTop ℝ≥0) (exit W N sample))) := fun t ↦
    NullCompleteFiltration.stronglyMeasurable_congr F μ hnull t (hm.stronglyAdapted t)
      (heq.mono fun sample hh ↦ hh t)
  exact hm.congr ha (fun t ↦ heq.mono fun sample hh ↦ (hh t).symm)

end SHEStochastic.UnboundedGlobalCylinderIdentification
