module

public import SHEStochastic.UnboundedGlobalNativeLawRecovery
public import SHEStochastic.GlobalBoundedComparison

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1400000
noncomputable section

namespace SHEStochastic.UnboundedGlobalNativeComparison
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

/-- Unbounded native uniqueness on any positive finite horizon,
reduced only to the explicit bounded native uniqueness theorem.
Continuation kernels, all stochastic characteristics, integrability,
uniform exits and vanishing exit tails are constructed internally.
The two continuation kernels may be chosen independently. -/
theorem laws_eq
    {Ω Ξ ι : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ] [Countable ι] [DecidableEq ι]
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
    (hBounded : ∀ R : ℕ, M ≤ R → GlobalBoundedComparison.Holds H hH
      (UnboundedCoefficientCutoff.holder hg R) hβ hβ1
      (UnboundedJointNativePasting.bound (G := g) (C := C) (β := β) R)
      (UnboundedCoefficientCutoff.bounded hg R) e u) :
    μ.map (NativeContinuousPath.path (H) W hcW) =
      ν.map (NativeContinuousPath.path (H) Z hcZ) := by
  obtain ⟨N, hN⟩ := exists_nat_ge M
  let levels (n : ℕ) := n+N
  have hlevels : Filter.Tendsto levels Filter.atTop Filter.atTop := by
    apply Filter.tendsto_atTop.mpr
    intro b
    exact Filter.eventually_atTop.mpr ⟨b, fun n hn ↦ hn.trans (Nat.le_add_right n N)⟩
  apply BorelStoppedLawLimit.laws_eq_cofinal (H)
    (L2ExtendedUniformNorm.realValue (haarAddCircle (T := 1))) (L2ExtendedUniformNorm.measurable_realValue _)
    μ ν (NativeContinuousPath.path (H) W hcW) (NativeContinuousPath.path (H) Z hcZ)
    (UnboundedGlobalContinuation.path_measurable F H W hW hcW)
    (UnboundedGlobalContinuation.path_measurable G H Z hZ hcZ) levels hlevels
  intro n
  let R := levels n
  have hR : M ≤ R := hN.trans (by exact_mod_cast (Nat.le_add_left N n))
  obtain ⟨QW, hlW, hbW, hsW⟩ := exists_closed F μ H W hW hg hβ hβ1 P e u hH hcW hnW heW
    M hM hu ell hell hel R hR
  obtain ⟨QZ, hlZ, hbZ, hsZ⟩ := exists_closed G ν H Z hZ hg hβ hβ1 P' e u hH hcZ hnZ heZ
    M hM hu ell hell hel R hR
  let μW := law F μ H W hW P hcW R QW
  let μZ := law G ν H Z hZ P' hcZ R QZ
  let PW := UnboundedGlobalNativeCharacteristics.family F μ H W hW hg hβ hβ1 P e u
    hH hcW hnW heW M hM hu R QW hlW hbW
  let PZ := UnboundedGlobalNativeCharacteristics.family G ν H Z hZ hg hβ hβ1 P' e u
    hH hcZ hnZ heZ M hM hu R QZ hlZ hbZ
  have hsame := hBounded R hR μW μZ PW PZ
    (UnboundedGlobalNativeLawRecovery.initial F μ H W hW hg hβ hβ1 P e u hH hcW hnW heW R QW)
    (UnboundedGlobalNativeLawRecovery.initial G ν H Z hZ hg hβ hβ1 P' e u hH hcZ hnZ heZ R QZ) hsW hsZ
  have hw := UnboundedGlobalNativeLawRecovery.stopped_law F μ H W hW hg hβ hβ1 P e u
    hH hcW hnW heW M hM hu R QW hlW hbW hsW
  have hz := UnboundedGlobalNativeLawRecovery.stopped_law G ν H Z hZ hg hβ hβ1 P' e u
    hH hcZ hnZ heZ M hM hu R QZ hlZ hbZ hsZ
  exact hw.symm.trans ((congrArg (fun m ↦ m.map (BorelObservablePath.stopped (H)
    (L2ExtendedUniformNorm.realValue (haarAddCircle (T := 1))) R)) hsame).trans hz)

end SHEStochastic.UnboundedGlobalNativeComparison
