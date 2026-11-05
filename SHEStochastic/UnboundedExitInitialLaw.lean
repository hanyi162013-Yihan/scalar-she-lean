module

public import SHEStochastic.UnboundedNativeContinuation

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 700000
noncomputable section

namespace SHEStochastic.UnboundedExitInitialLaw
open MeasureTheory ProbabilityTheory SHE SHE.PredictableL2 SHE.StoppedFourier SHE.DyadicApproximation SHE.FiniteHaar AddCircle
open UnboundedNativeHeatEquation UnboundedNativeUniformRegularity StoppedPathPasting
open scoped ENNReal NNReal

local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance : SecondCountableTopology CircleHeat.CircleL2 :=
  (_root_.fourierBasis (T := (1 : ℝ))).repr.toHomeomorph.secondCountableTopology
local instance : SecondCountableTopology RealL2 := realCircleIdentification.toHomeomorph.secondCountableTopology
local instance : MeasurableSpace RealL2 := borel _
local instance : BorelSpace RealL2 := ⟨rfl⟩
local instance (h : ℝ≥0) : Fact ((0 : ℝ) ≤ h) := ⟨h.property⟩

variable {Ω : Type*} [MeasurableSpace Ω]
  (H : ℝ≥0) (W : ℝ≥0 → Ω → RealL2) (hcW : ∀ sample, Continuous (fun t ↦ W t sample))

def value (N : ℕ) (sample : Ω) : RealL2 :=
  NativeContinuousPath.path (min H 1) W hcW sample (uniformExit H W hcW N sample)

theorem measurable_value (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›)
    (hW : StronglyMeasurable[F.predictable] (Function.uncurry W)) (N : ℕ) :
    Measurable (value H W hcW N) :=
  continuous_eval.measurable.comp
    ((UnboundedNativeContinuation.path_measurable F H W hW hcW).prodMk
      (UnboundedNativeContinuation.exit_measurable F H W hW hcW N))

def law (N : ℕ) (μ : Measure Ω) : Measure RealL2 := μ.map (value H W hcW N)

variable (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›)
  (hW : StronglyMeasurable[F.predictable] (Function.uncurry W))
  (μ : Measure Ω) [IsProbabilityMeasure μ]
  {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]
  {G : ℝ → V} {C β : ℝ≥0} (hG : HolderWith C β G) (hβ : 0 < β) (hβ1 : β < 1)
  {ι : Type*} [Countable ι] [DecidableEq ι] (P : FiniteScalarIto.Family F μ H ι)
  (e : HilbertBasis ι ℝ (Lp V 2 (haarAddCircle (T := 2 * Real.pi)))) (u₀ : RealL2)
  (hH : 0 < H) (hnull : NullCompleteFiltration.ContainsNullSets F μ)
  (hEquation : Equation F μ H W hW hG hβ hβ1 P e u₀)
  (M : ℝ) (hM : 0 ≤ M)
  (hu₀ : L2ExtendedUniformNorm.value (haarAddCircle (T := 1)) u₀ = ENNReal.ofReal M)

include hW in
theorem probability (N : ℕ) : IsProbabilityMeasure (law H W hcW N μ) :=
  (Measure.isProbabilityMeasure_map_iff (measurable_value H W hcW F hW N).aemeasurable).mpr inferInstance

include hH hnull hEquation hM hu₀ in
/-- The actual stopped state is uniformly L2 bounded, also at a terminal
exit without a hit. Its distribution is the random initial law needed
for bounded continuation; no global solution-law selection is needed. -/
theorem norm_bound (N : ℕ) (hN : M ≤ (N : ℝ)) :
    ∀ᵐ sample ∂μ, ‖value H W hcW N sample‖ ≤ N := by
  filter_upwards [UnboundedNativeUniformRegularity.exit_bound F μ H W hW hG hβ hβ1 P e u₀
    hH hcW hnull hEquation M hM hu₀ N hN] with sample hs
  have ha := (L2ExtendedUniformNorm.le_ofReal_iff (haarAddCircle (T := 1))
    (value H W hcW N sample) N (by positivity)).mp hs
  simpa [measureUnivNNReal] using Lp.norm_le_of_ae_bound (by positivity : (0 : ℝ) ≤ N) ha

include hH hnull hEquation hM hu₀ in
theorem memLp_value (N : ℕ) (hN : M ≤ (N : ℝ)) : MemLp (value H W hcW N) 2 μ :=
  MemLp.of_bound (measurable_value H W hcW F hW N).aestronglyMeasurable N
    (norm_bound H W hcW F hW μ hG hβ hβ1 P e u₀ hH hnull hEquation M hM hu₀ N hN)

include hH hnull hEquation hM hu₀ in
theorem memLp_identity (N : ℕ) (hN : M ≤ (N : ℝ)) :
    MemLp (id : RealL2 → RealL2) 2 (law H W hcW N μ) := by
  apply (memLp_map_measure_iff (by fun_prop) (measurable_value H W hcW F hW N).aemeasurable).mpr
  exact memLp_value H W hcW F hW μ hG hβ hβ1 P e u₀ hH hnull hEquation M hM hu₀ N hN

end SHEStochastic.UnboundedExitInitialLaw
