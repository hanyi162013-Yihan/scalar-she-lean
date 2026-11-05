module

public import SHEStochastic.NativePhysicalState
public import SHEStochastic.UnboundedLocalContinuousVersion
public import SHEStochastic.LocalizedRemainderObservation

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHEStochastic.UnboundedNativeHeatEquation
open MeasureTheory SHE SHE.PredictableL2 SHE.StoppedFourier SHE.DyadicApproximation AddCircle
open scoped NNReal ENNReal

local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩

variable {Ω V : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]

def physical (W : ℝ≥0 → Ω → RealL2) (p : ℝ≥0 × Ω) : Lp ℝ 2 (haarAddCircle (T := 2 * Real.pi)) :=
  NativePhysicalState.push (W p.1 p.2)

theorem physical_predictable (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›)
    (W : ℝ≥0 → Ω → RealL2) (hW : StronglyMeasurable[F.predictable] (Function.uncurry W)) :
    StronglyMeasurable[F.predictable] (physical W) := NativePhysicalState.push.continuous.comp_stronglyMeasurable hW

theorem physical_continuous (W : ℝ≥0 → Ω → RealL2) (hc : ∀ ω, Continuous (fun t ↦ W t ω)) (ω : Ω) :
    Continuous (fun t ↦ physical W (t, ω)) := NativePhysicalState.push.continuous.comp (hc ω)

def exit (W : ℝ≥0 → Ω → RealL2) (N : ℕ) : Ω → WithTop ℝ≥0 :=
  ContinuousNormExit.exit (fun t ω ↦ physical W (t, ω)) N

theorem exit_stopping (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›)
    (W : ℝ≥0 → Ω → RealL2) (hW : StronglyMeasurable[F.predictable] (Function.uncurry W))
    (hc : ∀ ω, Continuous (fun t ↦ W t ω)) (N : ℕ) : IsStoppingTime F (exit W N) :=
  UnboundedL2Localization.exit_stopping F (physical W) (physical_predictable F W hW) (physical_continuous W hc) N

variable (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
  (W : ℝ≥0 → Ω → RealL2) (hW : StronglyMeasurable[F.predictable] (Function.uncurry W))
  {G : ℝ → V} {C β : ℝ≥0} (hG : HolderWith C β G) (hβ : 0 < β) (hβ1 : β < 1)

def row (N : ℕ) (T : ℝ≥0) (hTH : T ≤ H) (hT : (T : ℝ) ≤ 1) (x : HeatCircle) :
    Process (E := Lp V 2 (haarAddCircle (T := 2 * Real.pi))) F μ H :=
  UnboundedHeatFamily.input F (UnboundedL2Localization.state (physical W) N)
    (UnboundedL2Localization.predictable F (physical W) (physical_predictable F W hW) N)
    hG hβ hβ1 μ H T hTH hT x (UnboundedL2Localization.history_bound (physical W) μ H N)

/-- The local positive-heat formulation on the original native state.
Each literal predictable input is localized in the spatial L2 norm;
there is no deterministic state bound, mild-remainder regularity or
uniqueness conclusion in this formulation. Translation from other weak
solution definitions remains a separate interface obligation. -/
def RandomEquation {ι : Type*} [Countable ι] [DecidableEq ι]
    (P : FiniteScalarIto.Family F μ H ι)
    (e : HilbertBasis ι ℝ (Lp V 2 (haarAddCircle (T := 2 * Real.pi)))) (ξ : Ω → RealL2) : Prop :=
  ∀ (N : ℕ) (T δ : ℝ≥0) (hTH : T ≤ H) (hT : (T : ℝ) ≤ 1) (hδ : 0 < δ)
    (hTD : T + δ ≤ H) (hTD1 : ((T + δ : ℝ≥0) : ℝ) ≤ 1) (x : HeatCircle),
    ∀ᵐ ω ∂μ, (T : WithTop ℝ≥0) < exit W N ω →
      NativeHeatObservation.functional δ x (W T ω) = NativeHeatObservation.functional (T + δ) x (ξ ω) +
        (FiniteCylindricalIto.terminalIto P.toCoordinates e).integral
          (StoppedItoInputs.stop F μ H T (row F μ H W hW hG hβ hβ1 N (T + δ) hTD hTD1 x)) ω

/-- Deterministic initial data are a specialization of the random-initial
native equation. The existing public interface is retained. -/
def Equation {ι : Type*} [Countable ι] [DecidableEq ι]
    (P : FiniteScalarIto.Family F μ H ι)
    (e : HilbertBasis ι ℝ (Lp V 2 (haarAddCircle (T := 2 * Real.pi)))) (u₀ : RealL2) : Prop :=
  RandomEquation F μ H W hW hG hβ hβ1 P e (fun _ ↦ u₀)

end SHEStochastic.UnboundedNativeHeatEquation
