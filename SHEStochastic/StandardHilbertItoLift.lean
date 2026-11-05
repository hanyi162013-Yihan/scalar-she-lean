module

public import SHE.StandardHilbertItoLift
public import SHEStochastic.HilbertTerminalIto
public import SHEStochastic.NoiseRestriction
public import SHEStochastic.CountableHilbertBasis

@[expose] public section
set_option autoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section

namespace SHEStochastic
open MeasureTheory SHE SHE.PredictableL2 SHE.HilbertColumns SHE.OrthogonalItoChannels
open scoped NNReal ENNReal

variable {Ω C ι κ E : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup C] [InnerProductSpace ℝ C]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [Countable κ]
  {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {μ : Measure Ω} {H : ℝ≥0}

def embeddedHilbertIto (J : StandardTerminalIto (C := C) (E := ℝ) 𝓕 μ H)
    (b : HilbertBasis κ ℝ E) (e : Space ι ℝ →ₗᵢ[ℝ] C) :
    StandardTerminalIto (C := Space ι E) (E := E) 𝓕 μ H :=
  HilbertTerminalIto.terminalIto 𝓕 μ H b (restrictNoise J e)

theorem embeddedHilbertIto_commutes (J : StandardTerminalIto (C := C) (E := ℝ) 𝓕 μ H)
    (b : HilbertBasis κ ℝ E) (e : Space ι ℝ →ₗᵢ[ℝ] C)
    (L : E →L[ℝ] ℝ) (v : Process (E := Space ι E) 𝓕 μ H) :
    (L.compLpL 2 μ) ((embeddedHilbertIto J b e).integral v) = J.integral
      (((e.toContinuousLinearMap.comp (mapCLM L)).compLpL 2
        ((energyMeasure μ H).trim (predictable_le_product 𝓕))) v) := by
  letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.predictable
  let ν := (energyMeasure μ H).trim (predictable_le_product 𝓕)
  have h := HilbertTerminalIto.commutes 𝓕 μ H b (restrictNoise J e) L v
  refine h.trans (congrArg J.integral ?_)
  apply Lp.ext
  filter_upwards [L2HilbertSum.lift_ae ν e (((mapCLM L).compLpL 2 ν) v),
    (mapCLM L).coeFn_compLpL v,
    (e.toContinuousLinearMap.comp (mapCLM L)).coeFn_compLpL v] with p he hL hc
  change L2HilbertSum.lift ν e (((mapCLM L).compLpL 2 ν) v) p =
    ((e.toContinuousLinearMap.comp (mapCLM L)).compLpL 2 ν) v p
  rw [he, hL, hc]
  rfl

end SHEStochastic

namespace SHEStochastic
open SHE SHE.HilbertColumns SHE.OrthogonalItoChannels
open scoped NNReal

/-- The old Hilbert-lift input is a theorem for every scalar terminal
isometry. No Novikov, Girsanov, BDG, or stochastic Fubini input is used. -/
theorem standardHilbertItoLift {Ω C : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup C] [InnerProductSpace ℝ C]
    {𝓕 : MeasureTheory.Filtration ℝ≥0 ‹MeasurableSpace Ω›}
    {μ : MeasureTheory.Measure Ω} {H : ℝ≥0}
    (J : StandardTerminalIto (C := C) (E := ℝ) 𝓕 μ H) : StandardHilbertItoLift J := by
  intro ι E _ _ _ _ _ e
  obtain ⟨w, b, _⟩ := exists_hilbertBasis (𝕜 := ℝ) (E := E)
  letI : Countable w := hilbertBasis_countable b
  exact ⟨embeddedHilbertIto J b (e.comp left), embeddedHilbertIto J b (e.comp right),
    embeddedHilbertIto_commutes J b (e.comp left), embeddedHilbertIto_commutes J b (e.comp right)⟩

end SHEStochastic
