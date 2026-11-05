module

public import SHEStochastic.UnboundedGlobalNativeComparison
public import SHEStochastic.GlobalBoundedComparisonProof
public import SHEStochastic.GlobalBoundedComparison

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1400000
noncomputable section

namespace SHEStochastic.UnboundedGlobalNativeUniqueness
open MeasureTheory ProbabilityTheory SHE SHE.PredictableL2 SHE.StoppedFourier SHE.DyadicApproximation SHE.FiniteHaar AddCircle
open UnboundedNativeHeatEquation UnboundedGlobalUniformRegularity StoppedPathPasting
open UnboundedGlobalNativeMildPasting
open scoped NNReal ENNReal Topology

local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
local instance : SecondCountableTopology CircleHeat.CircleL2 :=
  (_root_.fourierBasis (T := (1 : ℝ))).repr.toHomeomorph.secondCountableTopology
local instance : SecondCountableTopology RealL2 := realCircleIdentification.toHomeomorph.secondCountableTopology
local instance : MeasurableSpace RealL2 := borel _
local instance : BorelSpace RealL2 := ⟨rfl⟩

/-- Scalar unbounded uniqueness on every positive finite horizon with actual continuation,
pasting, bounded comparison and recovery all proved internally. -/
theorem laws_eq
    {Ω Ξ : Type*} {ι : Type} [MeasurableSpace Ω] [MeasurableSpace Ξ] [Countable ι] [DecidableEq ι]
    (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (G : Filtration ℝ≥0 ‹MeasurableSpace Ξ›)
    (μ : Measure Ω) (ν : Measure Ξ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (H : ℝ≥0) (hH : 0 < H)
    (W : ℝ≥0 → Ω → RealL2) (Z : ℝ≥0 → Ξ → RealL2)
    (hW : StronglyMeasurable[F.predictable] (Function.uncurry W))
    (hZ : StronglyMeasurable[G.predictable] (Function.uncurry Z))
    {g : ℝ → ℝ} {C β : ℝ≥0} (hg : HolderWith C β g) (hβ : 0 < β) (hβ1 : β < 1)
    (P : FiniteScalarIto.Family F μ H ι) (P' : FiniteScalarIto.Family G ν H ι)
    (e : HilbertBasis ι ℝ ScalarVarianceNormalization.Noise) (u : RealL2)
    (hcW : ∀ sample, Continuous (fun t ↦ W t sample))
    (hcZ : ∀ sample, Continuous (fun t ↦ Z t sample))
    (hnW : NullCompleteFiltration.ContainsNullSets F μ) (hnZ : NullCompleteFiltration.ContainsNullSets G ν)
    (heW : UnboundedGlobalNativeEquation.Equation F μ H W hW hg hβ hβ1 P e u)
    (heZ : UnboundedGlobalNativeEquation.Equation G ν H Z hZ hg hβ hβ1 P' e u)
    (M : ℝ) (hM : 0 ≤ M)
    (hu : L2ExtendedUniformNorm.value (haarAddCircle (T := 1)) u = ENNReal.ofReal M)
    (ell : ℝ) (hell : 0 < ell) (hel : ∀ z, ell ≤ (g z)^2)
 :
    μ.map (NativeContinuousPath.path (H) W hcW) =
      ν.map (NativeContinuousPath.path (H) Z hcZ) := by
  apply UnboundedGlobalNativeComparison.laws_eq F G μ ν H hH W Z hW hZ hg hβ hβ1 P P' e u
    hcW hcZ hnW hnZ heW heZ M hM hu ell hell hel
  intro R hR
  exact GlobalBoundedComparisonProof.holds H hH
    (UnboundedCoefficientCutoff.holder hg R) hβ hβ1
    (UnboundedJointNativePasting.bound (G := g) (C := C) (β := β) R)
    (UnboundedCoefficientCutoff.bounded hg R) e u ell hell
    (fun z ↦ hel (BallProjection.project R z))

end SHEStochastic.UnboundedGlobalNativeUniqueness
