module

public import SHEStochastic.UnboundedGlobalMildRecognition
public import SHEStochastic.GlobalMildUniformExit
public import SHEStochastic.UnboundedNativeMildRecognition
public import SHEStochastic.BorelObservableStopping
public import SHEStochastic.UniformCoefficientExit
public import SHE.NativeContinuousPath

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
noncomputable section

namespace SHEStochastic.UnboundedGlobalUniformRegularity
open MeasureTheory SHE SHE.PredictableL2 SHE.StoppedFourier SHE.DyadicApproximation SHE.FiniteHaar AddCircle Filter
open HeatParameterCover HeatParameterCoordinates HeatParameterPullback StoppedPathPasting AdaptedCanonicalPathTests
open UnboundedNativeHeatEquation
open scoped NNReal ENNReal Topology

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

def uniformExit (N : ℕ) (ω : Ω) : Time H :=
  UniformCoefficientExit.exit (haarAddCircle (T := 1)) H N
    (NativeContinuousPath.path H W hcW ω)

include hH hnull hEquation hM hu₀

/-- Uniform-norm continuity and finiteness on the actual entire horizon,
derived from the global localized native equation and bounded initial data. -/
theorem regularity : ∀ᵐ ω ∂μ,
    Continuous (fun t : Time H ↦ L2ExtendedUniformNorm.realValue (haarAddCircle (T:=1))
      (NativeContinuousPath.path H W hcW ω t)) ∧
    ∀ t : Time H, L2ExtendedUniformNorm.value (haarAddCircle (T:=1))
      (NativeContinuousPath.path H W hcW ω t)≠⊤ := by
  obtain ⟨Y,hYc,_,_,hzero,hrep⟩ := UnboundedGlobalMildRecognition.exists_closed_random_version
    F μ H W hW hG hβ hβ1 P e (fun _ ↦ u₀) hH hcW hnull hEquation
  filter_upwards [hzero,hrep] with ω hz hr
  let Q : C(Parameter,ℝ) := ⟨fun p ↦ Y p ω,hYc ω⟩
  apply GlobalMildUniformExit.regular_path H hH (NativeContinuousPath.path H W hcW ω) u₀ M hM hu₀ Q hz
  intro t
  let T : ℝ≥0 := t.val.toNNReal
  have ht : (T:ℝ)=t.val := Real.coe_toNNReal t.val t.property.1
  have hTH : T≤H := by change (T:ℝ)≤H; rw [ht]; exact t.property.2
  have hj : GlobalHeatRowPhysicalIntegration.unitTime H hH T hTH=GlobalHeatParameter.normalized H hH t := by
    apply Subtype.ext
    exact congrArg (fun r : ℝ ↦ r/(H:ℝ)) ht
  have hh := (congrArg NativePhysicalState.push (hr T hTH)).trans
    (NativeRemainderObservation.push_mild T.property u₀ Q (GlobalHeatRowPhysicalIntegration.unitTime H hH T hTH))
  rw [hj] at hh
  exact hh.trans (congrArg (fun s : ℝ ↦ PhysicalHeatState.state s (NativeHeatObservation.embed u₀)+
    PhysicalHeatParameterSection.value 2 Q (GlobalHeatParameter.normalized H hH t)) ht)

/-- The Borel uniform exit of the actual native solution is a genuine
stopping time, with its continuity premise now derived from the equation. -/
theorem isStoppingTime (N : ℕ) :
    IsStoppingTime F (fun ω ↦ (toNN H
      (BorelObservablePath.exit H (L2ExtendedUniformNorm.realValue (haarAddCircle (T := 1))) N
        (NativeContinuousPath.path H W hcW ω)) : WithTop ℝ≥0)) := by
  apply BorelObservableStopping.isStoppingTime_of_ae_continuous H μ F hnull
    (NativeContinuousPath.path H W hcW)
    (L2ExtendedUniformNorm.realValue (haarAddCircle (T := 1)))
    (L2ExtendedUniformNorm.measurable_realValue _) (fun ω t ↦ L2ExtendedUniformNorm.realValue_nonneg _ _) ?_ ?_ N
  · intro t
    change Measurable[F (toNN H t)] (fun ω ↦ W t.val.toNNReal ω)
    have ht : t.val.toNNReal = toNN H t := NNReal.eq (Real.coe_toNNReal t.val t.property.1)
    rw [ht]
    exact ((show IsStronglyPredictable F W from hW).stronglyAdapted _).measurable
  · exact (regularity F μ H W hW hG hβ hβ1 P e u₀ hH hcW hnull hEquation M hM hu₀).mono fun _ h ↦ h.1

theorem real_norm_initial : ∀ᵐ ω ∂μ,
    L2ExtendedUniformNorm.realValue (haarAddCircle (T := 1))
      (NativeContinuousPath.path H W hcW ω (origin H)) = M := by
  filter_upwards [UnboundedNativeMildRecognition.initial F μ H W hW hG hβ hβ1 P e u₀ hH hcW hnull
    (UnboundedGlobalNativeEquation.to_local F μ H W hW hG hβ hβ1 P e (fun _ ↦ u₀) hEquation)]
    with ω hi
  change L2ExtendedUniformNorm.realValue (haarAddCircle (T := 1)) (W (0 : ℝ).toNNReal ω) = M
  rw [Real.toNNReal_zero, hi]
  change (L2ExtendedUniformNorm.value (haarAddCircle (T := 1)) u₀).toReal = M
  rw [hu₀, ENNReal.toReal_ofReal hM]

theorem positive_exit (N : ℕ) (hN : M < (N : ℝ)) :
    ∀ᵐ ω ∂μ, origin H < uniformExit H W hcW N ω := by
  filter_upwards [regularity F μ H W hW hG hβ hβ1 P e u₀ hH hcW hnull hEquation M hM hu₀,
    real_norm_initial F μ H W hW hG hβ hβ1 P e u₀ hH hcW hnull hEquation M hM hu₀] with ω h hi
  apply UniformCoefficientExit.positive (haarAddCircle (T := 1)) H N
    (NativeContinuousPath.path H W hcW ω) h.1 hH
  rw [hi]
  exact hN

theorem attained (N : ℕ) (hN : M ≤ (N : ℝ)) : ∀ᵐ ω ∂μ,
    uniformExit H W hcW N ω ≠ ⊤ →
      L2ExtendedUniformNorm.value (haarAddCircle (T := 1))
        (NativeContinuousPath.path H W hcW ω (uniformExit H W hcW N ω)) = ENNReal.ofReal (N : ℝ) := by
  filter_upwards [regularity F μ H W hW hG hβ hβ1 P e u₀ hH hcW hnull hEquation M hM hu₀,
    real_norm_initial F μ H W hW hG hβ hβ1 P e u₀ hH hcW hnull hEquation M hM hu₀] with ω h hi hx
  apply UniformCoefficientExit.attained (haarAddCircle (T := 1)) H N
    (NativeContinuousPath.path H W hcW ω) h.1 h.2 ?_ hx
  rw [hi]
  exact hN

/-- The actual exit state is bounded even when the exit is the terminal
time without a hit. Its distribution can therefore initialize the
bounded continuation construction. -/
theorem exit_bound (N : ℕ) (hN : M ≤ (N : ℝ)) : ∀ᵐ sample ∂μ,
    L2ExtendedUniformNorm.value (haarAddCircle (T := 1))
      (NativeContinuousPath.path H W hcW sample (uniformExit H W hcW N sample)) ≤
        ENNReal.ofReal (N : ℝ) := by
  filter_upwards [regularity F μ H W hW hG hβ hβ1 P e u₀ hH hcW hnull hEquation M hM hu₀,
    real_norm_initial F μ H W hW hG hβ hβ1 P e u₀ hH hcW hnull hEquation M hM hu₀]
    with sample hs hi
  apply UniformCoefficientExit.bound_at_exit (haarAddCircle (T := 1)) H N
    (NativeContinuousPath.path H W hcW sample) hs.1 hs.2
  rw [hi]
  exact hN

/-- The actual unbounded solution has the original and radially cut
coefficients equal almost everywhere in space before its uniform exit.
This is the coefficient agreement needed for martingale pasting. -/
theorem coefficient_agrees (N : ℕ) : ∀ᵐ ω ∂μ, ∀ t : Time H,
    t < uniformExit H W hcW N ω →
      (fun a ↦ UnboundedCoefficientCutoff.coefficient G N
        (NativeContinuousPath.path H W hcW ω t a)) =ᵐ[haarAddCircle (T := 1)]
      fun a ↦ G (NativeContinuousPath.path H W hcW ω t a) := by
  exact (regularity F μ H W hW hG hβ hβ1 P e u₀ hH hcW hnull hEquation M hM hu₀).mono fun ω h t ht ↦
    UniformCoefficientExit.coefficient_agrees (haarAddCircle (T := 1)) H N
      (NativeContinuousPath.path H W hcW ω) h.1 h.2 G t ht

end SHEStochastic.UnboundedGlobalUniformRegularity
