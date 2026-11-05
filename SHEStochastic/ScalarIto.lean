module

public import SHE.StandardTerminalIto
public import MathFin.Foundations.ItoIntegralLocality

/-!
Adapt the public MathFin scalar Itô construction to the SHE terminal-integral
interface. The construction uses the natural filtration of a real Brownian
motion; arbitrary filtrations and cylindrical noise are separate extensions.
-/

@[expose] public section
noncomputable section

namespace SHEStochastic
open MeasureTheory Set
open scoped NNReal

theorem timeMeasure_eq (T : ℝ≥0) :
    SHE.PredictableL2.timeMeasure T = MathFin.ItoIntegralCLM.timeMeasure_T T := by
  unfold SHE.PredictableL2.timeMeasure MathFin.ItoIntegralCLM.timeMeasure_T
    MathFin.ItoIntegralL2.timeMeasure
  rw [SHE.PredictableL2.nonnegative_coe_measurableEmbedding.comap_restrict]
  rfl

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
  [IsProbabilityMeasure μ] {B : ℝ≥0 → Ω → ℝ}

open SHE.PredictableL2 MathFin.ItoIntegralL2 MathFin.ItoIntegralCLM
  MathFin.ItoIntegralProcessGeneral

theorem processMeasure_eq (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t)) :
    (energyMeasure μ T).trim (predictable_le_product (natFiltration hBmeas)) =
      trimMeasure_T (μ := μ) T hBmeas := by
  unfold energyMeasure trimMeasure_T
  rw [timeMeasure_eq]

/-- Identity transport between the two existing predictable-L² conventions. -/
def processTransport (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t)) :
    Process (E := ℝ) (natFiltration hBmeas) μ T →ₗᵢ[ℝ]
      Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas) := by
  letI : MeasurableSpace (ℝ≥0 × Ω) := (natFiltration hBmeas).predictable
  exact Lp.compMeasurePreservingₗᵢ ℝ id
    ⟨measurable_id, by rw [Measure.map_id]; exact (processMeasure_eq T hBmeas).symm⟩

theorem processTransport_ae (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
    (v : Process (E := ℝ) (natFiltration hBmeas) μ T) :
    processTransport T hBmeas v =ᵐ[trimMeasure_T (μ := μ) T hBmeas] v := by
  letI : MeasurableSpace (ℝ≥0 × Ω) := (natFiltration hBmeas).predictable
  exact Lp.coeFn_compMeasurePreserving _ _

/-- The actual scalar terminal Itô isometry, constructed by density upstream. -/
def scalarIntegral (hB : ProbabilityTheory.IsPreBrownianReal B μ) (T : ℝ≥0)
    (hBmeas : ∀ t, Measurable (B t)) :
    Process (E := ℝ) (natFiltration hBmeas) μ T →ₗᵢ[ℝ] Lp ℝ 2 μ :=
  ({ (itoIntegralCLM_T hB T hBmeas).toLinearMap with
      norm_map' := itoIntegralCLM_T_norm hB T hBmeas } :
      Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas) →ₗᵢ[ℝ] Lp ℝ 2 μ).comp
    (processTransport T hBmeas)

theorem scalarIntegral_centered (hB : ProbabilityTheory.IsPreBrownianReal B μ)
    (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
    (v : Process (E := ℝ) (natFiltration hBmeas) μ T) :
    ∫ ω, scalarIntegral hB T hBmeas v ω ∂μ = 0 :=
  integral_itoIntegralCLM_T hB T hBmeas _

theorem processTransport_stopped (T l : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
    (v : Process (E := ℝ) (natFiltration hBmeas) μ T)
    (hv : ∀ᵐ p ∂energyMeasure μ T, l < p.1 → v p = 0) :
    ∀ᵐ p ∂trimMeasure_T (μ := μ) T hBmeas,
      l < p.1 → processTransport T hBmeas v p = 0 := by
  let S : Set (ℝ≥0 × Ω) := Set.Ioi l ×ˢ Set.univ
  have hS : MeasurableSet[(natFiltration hBmeas).predictable] S :=
    measurableSet_predictable_Ioi_prod MeasurableSet.univ
  have hzero : S.indicator (v : ℝ≥0 × Ω → ℝ) =ᵐ[energyMeasure μ T] fun _ => 0 := by
    filter_upwards [hv] with p hp
    by_cases h : p ∈ S
    · rw [Set.indicator_of_mem h, hp h.1]
    · exact Set.indicator_of_notMem h _
  have htrim := ae_eq_trim_of_measurable (predictable_le_product (natFiltration hBmeas))
    ((Lp.stronglyMeasurable v).measurable.indicator hS) measurable_const hzero
  have hle : ae (trimMeasure_T (μ := μ) T hBmeas) ≤
      ae ((energyMeasure μ T).trim (predictable_le_product (natFiltration hBmeas))) := by
    rw [processMeasure_eq T hBmeas]
  filter_upwards [processTransport_ae T hBmeas v, htrim.filter_mono hle] with p hp hz hl
  rw [hp]
  simpa only [Set.indicator_of_mem (show p ∈ S from ⟨hl, Set.mem_univ _⟩)] using hz

/-- The scalar/natural-filtration instance of stochastic input package 1. -/
def scalarTerminalIto (hB : ProbabilityTheory.IsPreBrownianReal B μ) (T : ℝ≥0)
    (hBmeas : ∀ t, Measurable (B t)) :
    SHE.StandardTerminalIto (C := ℝ) (E := ℝ) (natFiltration hBmeas) μ T where
  integral := scalarIntegral hB T hBmeas
  centered := scalarIntegral_centered hB T hBmeas
  adapted l v hv := by
    have hmeas : AEStronglyMeasurable[natFiltration hBmeas l]
        (scalarIntegral hB T hBmeas v : Ω → ℝ) μ := by
      by_cases hl : l ≤ T
      · have heq := MathFin.itoIntegralCLM_T_eq_itoProcessCLM_of_vanishes_after
          hB T l hl hBmeas (processTransport T hBmeas v)
          (processTransport_stopped T l hBmeas v hv)
        change AEStronglyMeasurable[natFiltration hBmeas l]
          (itoIntegralCLM_T hB T hBmeas (processTransport T hBmeas v) : Ω → ℝ) μ
        rw [heq]
        exact itoProcessCLM_aeStronglyMeasurable hB T l hBmeas _
      · have ht := itoProcessCLM_aeStronglyMeasurable hB T T hBmeas
          (processTransport T hBmeas v)
        rw [itoProcessCLM_terminal_eq] at ht
        exact ht.mono ((natFiltration hBmeas).mono (le_of_not_ge hl))
    exact ⟨hmeas.mk _, hmeas.stronglyMeasurable_mk, hmeas.ae_eq_mk⟩

end SHEStochastic
