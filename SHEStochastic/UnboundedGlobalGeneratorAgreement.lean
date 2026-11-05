module

public import SHEStochastic.UnboundedGlobalUniformRegularity
public import SHEStochastic.FourierCylinderGenerator
public import SHEStochastic.PastedGeneratorFunctional

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
noncomputable section

namespace SHEStochastic.UnboundedGlobalGeneratorAgreement
open MeasureTheory SHE SHE.PredictableL2 SHE.StoppedFourier SHE.DyadicApproximation SHE.FiniteHaar AddCircle Filter
open StoppedPathPasting UnboundedNativeHeatEquation UnboundedGlobalUniformRegularity
open scoped NNReal ENNReal

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
  (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
  (W : ℝ≥0 → Ω → RealL2) (hW : StronglyMeasurable[F.predictable] (Function.uncurry W))
  {G : ℝ → V} {C β : ℝ≥0} (hG : HolderWith C β G) (hβ : 0 < β) (hβ1 : β < 1)
  {ι : Type*} [Countable ι] [DecidableEq ι]
  (P : FiniteScalarIto.Family F μ H ι)
  (e : HilbertBasis ι ℝ (Lp V 2 (haarAddCircle (T := 2 * Real.pi)))) (u₀ : RealL2)
  (hH : 0 < H) (hcW : ∀ ω, Continuous (fun t ↦ W t ω))
  (hnull : NullCompleteFiltration.ContainsNullSets F μ)
  (hEquation : UnboundedGlobalNativeEquation.Equation F μ H W hW hG hβ hβ1 P e u₀)
  (M : ℝ) (hM : 0 ≤ M)
  (hu₀ : L2ExtendedUniformNorm.value (haarAddCircle (T := 1)) u₀ = ENNReal.ofReal M)
  {d : ℕ} (f : GaussianItoTest.State d → ℝ) (hf : ContDiff ℝ 2 f) (hs : HasCompactSupport f)
  (a : Fin d → ℂ →L[ℝ] ℝ) (n : Fin d → ℤ)

include hH hnull hEquation hM hu₀

/-- The native equation implies exact agreement of the original and
bounded-cutoff Fourier cylinder generators before the actual uniform
exit. The statement holds simultaneously at all times on the interval. -/
theorem generator_agrees (N : ℕ) : ∀ᵐ ω ∂μ, ∀ t : Time H,
    t < uniformExit H W hcW N ω →
      FourierCylinderGenerator.generator f hf hs hG hβ hβ1.le N a n
        (NativeContinuousPath.path H W hcW ω t) =
      FourierCylinderGenerator.value f hG hβ hβ1.le a n
        (NativeContinuousPath.path H W hcW ω t) := by
  filter_upwards [regularity F μ H W hW hG hβ hβ1 P e u₀ hH hcW hnull hEquation M hM hu₀]
    with ω hreg t ht
  let u := NativeContinuousPath.path H W hcW ω t
  have hb := UniformCoefficientExit.before_bound (haarAddCircle (T := 1)) H N
    (NativeContinuousPath.path H W hcW ω) hreg.1 hreg.2 t ht
  have hp : L2ExtendedUniformNorm.value haarAddCircle (NativePhysicalState.push u) ≤ ENNReal.ofReal (N : ℝ) :=
    (NativePhysicalState.uniform_norm_push u).trans_le hb
  exact FourierCylinderGenerator.generator_agrees f hf hs hG hβ hβ1.le N a n u
    ((L2ExtendedUniformNorm.le_ofReal_iff haarAddCircle (NativePhysicalState.push u) N (by positivity)).mp hp)

/-- The entire stopped canonical martingale functional agrees, including
its time integral. This is the exact generator replacement used when
pasting a bounded continuation onto an unbounded native solution. -/
theorem canonical_value_agrees (N : ℕ) : ∀ᵐ ω ∂μ, ∀ t : Time H,
    PastedGeneratorFunctional.value H (FourierCylinderGenerator.test f hf hs a n)
      (FourierCylinderGenerator.generator f hf hs hG hβ hβ1.le N a n)
      (NativeContinuousPath.path H W hcW ω)
      (pastTime H (uniformExit H W hcW N ω) t) =
    PastedGeneratorFunctional.value H (FourierCylinderGenerator.test f hf hs a n)
      (FourierCylinderGenerator.value f hG hβ hβ1.le a n)
      (NativeContinuousPath.path H W hcW ω)
      (pastTime H (uniformExit H W hcW N ω) t) := by
  filter_upwards [generator_agrees F μ H W hW hG hβ hβ1 P e u₀ hH hcW hnull hEquation M hM hu₀ f hf hs a n N]
    with ω hω t
  exact PastedGeneratorFunctional.value_congr_before H
    (FourierCylinderGenerator.test f hf hs a n)
    (FourierCylinderGenerator.generator f hf hs hG hβ hβ1.le N a n)
    (FourierCylinderGenerator.value f hG hβ hβ1.le a n)
    (uniformExit H W hcW N ω) t (NativeContinuousPath.path H W hcW ω) hω

end SHEStochastic.UnboundedGlobalGeneratorAgreement
