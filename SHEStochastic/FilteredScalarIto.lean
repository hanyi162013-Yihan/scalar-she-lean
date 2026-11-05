module

public import SHEStochastic.ScalarIto
public import SHEStochastic.FilteredItoStopping

/-! The scalar SHE terminal-integral interface in any full Brownian filtration. -/

@[expose] public section
noncomputable section
namespace SHEStochastic.FilteredScalarIto
open MeasureTheory Set ProbabilityTheory
open scoped NNReal
open SHE.PredictableL2 FilteredItoCLM FilteredItoProcessGeneral
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
  [IsProbabilityMeasure μ] {B : ℝ≥0 → Ω → ℝ}
  {𝓖 : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
  [hFB : IsFilteredPreBrownian B 𝓖 μ]

omit hFB in
theorem processMeasure_eq (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t)) :
    (energyMeasure μ T).trim (predictable_le_product 𝓖) =
      trimMeasure_T (𝓖 := 𝓖) (μ := μ) T hBmeas := by
  unfold energyMeasure trimMeasure_T
  rw [timeMeasure_eq]

omit hFB in
def processTransport (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t)) :
    Process (E := ℝ) 𝓖 μ T →ₗᵢ[ℝ]
      Lp ℝ 2 (trimMeasure_T (𝓖 := 𝓖) (μ := μ) T hBmeas) := by
  letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓖.predictable
  exact Lp.compMeasurePreservingₗᵢ ℝ id
    ⟨measurable_id, by rw [Measure.map_id]; exact (processMeasure_eq (𝓖 := 𝓖) T hBmeas).symm⟩

omit hFB in
theorem processTransport_ae (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
    (v : Process (E := ℝ) 𝓖 μ T) :
    processTransport (𝓖 := 𝓖) T hBmeas v =ᵐ[trimMeasure_T (𝓖 := 𝓖) (μ := μ) T hBmeas] v := by
  letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓖.predictable
  exact Lp.coeFn_compMeasurePreserving _ _

def scalarIntegral (hB : ProbabilityTheory.IsPreBrownianReal B μ) (T : ℝ≥0)
    (hBmeas : ∀ t, Measurable (B t)) :
    Process (E := ℝ) 𝓖 μ T →ₗᵢ[ℝ] Lp ℝ 2 μ :=
  ({ (itoIntegralCLM_T (𝓖 := 𝓖) hB T hBmeas).toLinearMap with
      norm_map' := itoIntegralCLM_T_norm (𝓖 := 𝓖) hB T hBmeas } :
      Lp ℝ 2 (trimMeasure_T (𝓖 := 𝓖) (μ := μ) T hBmeas) →ₗᵢ[ℝ] Lp ℝ 2 μ).comp
    (processTransport (𝓖 := 𝓖) T hBmeas)

theorem scalarIntegral_centered (hB : ProbabilityTheory.IsPreBrownianReal B μ)
    (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
    (v : Process (E := ℝ) 𝓖 μ T) :
    ∫ ω, scalarIntegral (𝓖 := 𝓖) hB T hBmeas v ω ∂μ = 0 :=
  integral_itoIntegralCLM_T (𝓖 := 𝓖) hB T hBmeas _

omit hFB in
theorem processTransport_stopped (T l : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
    (v : Process (E := ℝ) 𝓖 μ T)
    (hv : ∀ᵐ p ∂energyMeasure μ T, l < p.1 → v p = 0) :
    ∀ᵐ p ∂trimMeasure_T (𝓖 := 𝓖) (μ := μ) T hBmeas,
      l < p.1 → processTransport (𝓖 := 𝓖) T hBmeas v p = 0 := by
  let S : Set (ℝ≥0 × Ω) := Set.Ioi l ×ˢ Set.univ
  have hS : MeasurableSet[𝓖.predictable] S :=
    measurableSet_predictable_Ioi_prod MeasurableSet.univ
  have hzero : S.indicator (v : ℝ≥0 × Ω → ℝ) =ᵐ[energyMeasure μ T] fun _ => 0 := by
    filter_upwards [hv] with p hp
    by_cases h : p ∈ S
    · rw [Set.indicator_of_mem h, hp h.1]
    · exact Set.indicator_of_notMem h _
  have htrim := ae_eq_trim_of_measurable (predictable_le_product 𝓖)
    ((Lp.stronglyMeasurable v).measurable.indicator hS) measurable_const hzero
  have hle : ae (trimMeasure_T (𝓖 := 𝓖) (μ := μ) T hBmeas) ≤
      ae ((energyMeasure μ T).trim (predictable_le_product 𝓖)) := by
    rw [processMeasure_eq (𝓖 := 𝓖) T hBmeas]
  filter_upwards [processTransport_ae (𝓖 := 𝓖) T hBmeas v, htrim.filter_mono hle] with p hp hz hl
  rw [hp]
  simpa only [Set.indicator_of_mem (show p ∈ S from ⟨hl, Set.mem_univ _⟩)] using hz

def terminalIto (hB : ProbabilityTheory.IsPreBrownianReal B μ) (T : ℝ≥0)
    (hBmeas : ∀ t, Measurable (B t)) :
    SHE.StandardTerminalIto (C := ℝ) (E := ℝ) 𝓖 μ T where
  integral := scalarIntegral (𝓖 := 𝓖) hB T hBmeas
  centered := scalarIntegral_centered (𝓖 := 𝓖) hB T hBmeas
  adapted l v hv := by
    have hmeas : AEStronglyMeasurable[𝓖 l]
        (scalarIntegral (𝓖 := 𝓖) hB T hBmeas v : Ω → ℝ) μ := by
      by_cases hl : l ≤ T
      · have heq := FilteredItoProcessGeneral.itoIntegralCLM_T_eq_itoProcessCLM_of_vanishes_after (𝓖 := 𝓖)
          hB T l hl hBmeas (processTransport (𝓖 := 𝓖) T hBmeas v)
          (processTransport_stopped (𝓖 := 𝓖) T l hBmeas v hv)
        change AEStronglyMeasurable[𝓖 l]
          (itoIntegralCLM_T (𝓖 := 𝓖) hB T hBmeas (processTransport (𝓖 := 𝓖) T hBmeas v) : Ω → ℝ) μ
        rw [heq]
        exact itoProcessCLM_aeStronglyMeasurable (𝓖 := 𝓖) hB T l hBmeas _
      · have ht := itoProcessCLM_aeStronglyMeasurable (𝓖 := 𝓖) hB T T hBmeas
          (processTransport (𝓖 := 𝓖) T hBmeas v)
        rw [itoProcessCLM_terminal_eq (𝓖 := 𝓖)] at ht
        exact ht.mono (𝓖.mono (le_of_not_ge hl))
    exact ⟨hmeas.mk _, hmeas.stronglyMeasurable_mk, hmeas.ae_eq_mk⟩

/-- Construction of scalar predictable integration from a real Brownian
motion recognized in the given full filtration. No stochastic integral,
Itô formula, BDG bound, or change-of-measure theorem is an input. -/
def ofFilteredBrownian (T : ℝ≥0) :
    SHE.StandardTerminalIto (C := ℝ) (E := ℝ) 𝓖 μ T :=
  terminalIto hFB.toIsPreBrownianReal T
    (fun t ↦ (hFB.stronglyAdapted t).measurable.mono (𝓖.le t) le_rfl)


end SHEStochastic.FilteredScalarIto
