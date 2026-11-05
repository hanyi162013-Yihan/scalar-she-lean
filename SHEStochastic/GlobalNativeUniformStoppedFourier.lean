module

public import SHEStochastic.UnboundedGlobalExitInitialLaw
public import SHEStochastic.NativeUniformStoppedFourier
public import SHEStochastic.UnboundedGlobalFourierStoppedMartingale
public import SHEStochastic.BoundedLocalMartingale

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1200000
noncomputable section

namespace SHEStochastic.GlobalNativeUniformStoppedFourier
open MeasureTheory ProbabilityTheory SHE SHE.PredictableL2 SHE.StoppedFourier SHE.DyadicApproximation SHE.FiniteHaar AddCircle Filter
open UnboundedNativeHeatEquation UnboundedGlobalUniformRegularity StoppedPathPasting
open scoped NNReal ENNReal

local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
local instance : MeasurableSpace RealL2 := borel _
local instance : BorelSpace RealL2 := ⟨rfl⟩
local instance : SecondCountableTopology CircleHeat.CircleL2 :=
  (_root_.fourierBasis (T := (1 : ℝ))).repr.toHomeomorph.secondCountableTopology
local instance : SecondCountableTopology RealL2 := realCircleIdentification.toHomeomorph.secondCountableTopology

variable {Ω V ι : Type*} [MeasurableSpace Ω] [Countable ι] [DecidableEq ι]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]
  (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
  (W : ℝ≥0 → Ω → RealL2) (hW : StronglyMeasurable[F.predictable] (Function.uncurry W))
  {G : ℝ → V} {C β : ℝ≥0} (hG : HolderWith C β G) (hβ : 0 < β) (hβ1 : β < 1)
  (P : FiniteScalarIto.Family F μ H ι)
  (e : HilbertBasis ι ℝ (Lp V 2 (haarAddCircle (T := 2 * Real.pi)))) (u₀ : RealL2)
  (hH : 0 < H) (hcW : ∀ ω, Continuous (fun t ↦ W t ω))
  (hnull : NullCompleteFiltration.ContainsNullSets F μ)
  (hEquation : UnboundedGlobalNativeEquation.Equation F μ H W hW hG hβ hβ1 P e u₀)
  (M : ℝ) (hM : 0 ≤ M)
  (hu₀ : L2ExtendedUniformNorm.value (haarAddCircle (T := 1)) u₀ = ENNReal.ofReal M)

include hH hnull hEquation hM hu₀ in
theorem state_bound (R : ℕ) (hR : M ≤ R) :
    ∀ᵐ ω ∂μ, ∀ t : Time H, t ≤ uniformExit H W hcW R ω →
      ‖NativeContinuousPath.path H W hcW ω t‖ ≤ R := by
  filter_upwards [regularity F μ H W hW hG hβ hβ1 P e u₀ hH hcW hnull hEquation M hM hu₀,
    real_norm_initial F μ H W hW hG hβ hβ1 P e u₀ hH hcW hnull hEquation M hM hu₀]
    with ω hreg hzero t ht
  have hb := UniformCoefficientExit.before_or_at_bound (haarAddCircle (T := 1)) H R
    (NativeContinuousPath.path H W hcW ω) hreg.1 hreg.2 (hzero.trans_le hR) t ht
  have ha := (L2ExtendedUniformNorm.le_ofReal_iff (haarAddCircle (T := 1))
    (NativeContinuousPath.path H W hcW ω t) R (by positivity)).mp hb
  simpa [measureUnivNNReal] using Lp.norm_le_of_ae_bound (by positivity : (0 : ℝ) ≤ R) ha

include hH hnull hEquation hM hu₀ in
/-- The actual Fourier fluctuation stopped at its uniform exit is a
genuine martingale. The L2 localization is removed by the derived
almost-sure deterministic bound, not by a new integrability hypothesis. -/
theorem martingale (R : ℕ) (hR : M ≤ R) (a : ℂ →L[ℝ] ℝ) (n : ℤ) :
    Martingale (stoppedProcess (NativeUniformStoppedFourier.coordinate W a n)
      (fun ω ↦ (AdaptedCanonicalPathTests.toNN H (uniformExit H W hcW R ω) : WithTop ℝ≥0))) F μ := by
  exact NativeUniformStoppedFourier.martingale_of_stopped F μ W hW u₀ hcW H (uniformExit H W hcW R) R a n
    (UnboundedGlobalUniformRegularity.isStoppingTime F μ H W hW hG hβ hβ1 P e u₀
      hH hcW hnull hEquation M hM hu₀ R)
    (UnboundedNativeMildRecognition.initial F μ H W hW hG hβ hβ1 P e u₀ hH hcW hnull
      (UnboundedGlobalNativeEquation.to_local F μ H W hW hG hβ hβ1 P e (fun _ ↦ u₀) hEquation))
    (fun N ↦ UnboundedGlobalFourierStoppedMartingale.martingale F μ H W hW hG hβ hβ1 P e u₀
      hH hcW hnull hEquation N a n)
    (state_bound F μ H W hW hG hβ hβ1 P e u₀ hH hcW hnull hEquation M hM hu₀ R hR)

end SHEStochastic.GlobalNativeUniformStoppedFourier
