module

public import SHEStochastic.UnboundedFiniteHorizonInput
public import SHEStochastic.UnboundedNativeHeatEquation

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHEStochastic.UnboundedGlobalNativeEquation
open MeasureTheory SHE SHE.PredictableL2 SHE.StoppedFourier SHE.DyadicApproximation AddCircle
open UnboundedNativeHeatEquation
open scoped NNReal ENNReal

local instance : Fact (0<2*Real.pi) := ⟨by positivity⟩

variable {Ω V : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]
  (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
  (W : ℝ≥0 → Ω → RealL2) (hW : StronglyMeasurable[F.predictable] (Function.uncurry W))
  {G : ℝ → V} {C β : ℝ≥0} (hG : HolderWith C β G) (hβ : 0<β) (hβ1 : β<1)

/-- The same localized heat row as in the short-time equation, defined
for every observation time on the original finite native horizon. -/
def row (N : ℕ) (T : ℝ≥0) (hTH : T≤H) (x : HeatCircle) :
    Process (E := Lp V 2 (haarAddCircle (T := 2*Real.pi))) F μ H :=
  UnboundedFiniteHorizonInput.input F (UnboundedL2Localization.state (physical W) N)
    (UnboundedL2Localization.predictable F (physical W) (physical_predictable F W hW) N)
    hG hβ hβ1 μ H T hTH x (UnboundedL2Localization.history_bound (physical W) μ H N)

/-- Global localized positive-heat formulation. Unlike the original
unit-time interface, it tests all T+δ≤H. Neither path regularity beyond
L2 nor a comparison/uniqueness conclusion is assumed here. -/
def RandomEquation {ι : Type*} [Countable ι] [DecidableEq ι]
    (P : FiniteScalarIto.Family F μ H ι)
    (e : HilbertBasis ι ℝ (Lp V 2 (haarAddCircle (T := 2*Real.pi)))) (ξ : Ω → RealL2) : Prop :=
  ∀ (N : ℕ) (T δ : ℝ≥0) (hTH : T≤H) (hδ : 0<δ) (hTD : T+δ≤H) (x : HeatCircle),
    ∀ᵐ ω ∂μ, (T : WithTop ℝ≥0)<exit W N ω →
      NativeHeatObservation.functional δ x (W T ω)=NativeHeatObservation.functional (T+δ) x (ξ ω)+
        (FiniteCylindricalIto.terminalIto P.toCoordinates e).integral
          (StoppedItoInputs.stop F μ H T (row F μ H W hW hG hβ hβ1 N (T+δ) hTD x)) ω

def Equation {ι : Type*} [Countable ι] [DecidableEq ι]
    (P : FiniteScalarIto.Family F μ H ι)
    (e : HilbertBasis ι ℝ (Lp V 2 (haarAddCircle (T := 2*Real.pi)))) (u : RealL2) : Prop :=
  RandomEquation F μ H W hW hG hβ hβ1 P e (fun _ ↦ u)

/-- Exact compatibility with the already proved local equation; the
native integrals agree, rather than merely having the same law. -/
theorem to_local {ι : Type*} [Countable ι] [DecidableEq ι]
    (P : FiniteScalarIto.Family F μ H ι)
    (e : HilbertBasis ι ℝ (Lp V 2 (haarAddCircle (T := 2*Real.pi)))) (ξ : Ω → RealL2)
    (h : RandomEquation F μ H W hW hG hβ hβ1 P e ξ) :
    UnboundedNativeHeatEquation.RandomEquation F μ H W hW hG hβ hβ1 P e ξ := by
  intro N T δ hTH hT hδ hTD hTD1 x
  exact h N T δ hTH hδ hTD x

end SHEStochastic.UnboundedGlobalNativeEquation
