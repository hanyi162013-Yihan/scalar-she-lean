module

public import SHEStochastic.FiniteCylindricalIto
public import SHEStochastic.FiniteScalarTerminalIto

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section

namespace SHEStochastic.FiniteCylindricalIto
open MeasureTheory SHE SHE.PredictableL2
open scoped NNReal ENNReal Topology
variable {Ω ι C : Type*} [MeasurableSpace Ω] [Countable ι] [DecidableEq ι]
  [NormedAddCommGroup C] [InnerProductSpace ℝ C] [CompleteSpace C]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {μ : Measure Ω} [IsProbabilityMeasure μ] {H : ℝ≥0}
local notation "ν" => FiniteScalarIto.inputMeasure F μ H

theorem sourceEquiv_coordinate (e : HilbertBasis ι ℝ C) (v : Lp C 2 ν) (i : ι) :
    letI : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
    sourceEquiv e v i = (innerSL ℝ (e i)).compLpL 2 ν v := by
  letI : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
  change (L2HilbertSum.total ν (ColumnsHilbertSum.unit e)
    (ColumnsHilbertSum.unit_total e)).linearIsometryEquiv v i = _
  rw [L2HilbertSum.coordinate, L2HilbertSum.lift_adjoint ν (ColumnsHilbertSum.unit e) i,
    ColumnsHilbertSum.unit_adjoint]

theorem rawIntegral_adapted (P : FiniteScalarIto.Coordinates F μ H ι) (e : HilbertBasis ι ℝ C)
    (t : ℝ≥0) (v : Lp C 2 ν) (hv : ∀ᵐ p ∂ν, t < p.1 → v p = 0) :
    AEStronglyMeasurable[F t] (rawIntegral P e v : Ω → ℝ) μ := by
  classical
  letI : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
  let f := sourceEquiv e v
  have hf (i : ι) : ∀ᵐ p ∂ν, t < p.1 → f i p = 0 := by
    change ∀ᵐ p ∂ν, t < p.1 → sourceEquiv e v i p = 0
    rw [sourceEquiv_coordinate]
    filter_upwards [(innerSL ℝ (e i)).coeFn_compLpL v, hv] with p hp hz ht
    rw [hp, hz ht, map_zero]
  have hY (i : ι) : AEStronglyMeasurable[F t] (FiniteScalarIto.rawIsometry P i (f i) : Ω → ℝ) μ := by
    by_cases ht : t ≤ H
    · rw [FiniteScalarItoProcess.rawIsometry_eq_prefix_of_vanishes_after P i t ht (f i) (hf i)]
      exact FiniteScalarItoProcess.prefixCLM_adapted P i t (f i)
    · have h := FiniteScalarItoProcess.prefixCLM_adapted P i H (f i)
      rw [FiniteScalarItoProcess.prefixCLM_terminal] at h
      exact h.mono (F.mono (le_of_not_ge ht))
  have hs (s : Finset ι) :
      AEStronglyMeasurable[F t] (∑ i ∈ s, FiniteScalarIto.rawIsometry P i (f i) : Lp ℝ 2 μ) μ := by
    apply (mem_lpMeas_iff_aestronglyMeasurable (𝕜 := ℝ)).mp
    exact Submodule.sum_mem (lpMeas ℝ ℝ (F t) 2 μ)
      (fun i _ ↦ mem_lpMeas_iff_aestronglyMeasurable.mpr (hY i))
  exact (isClosed_aestronglyMeasurable (F.le t)).mem_of_tendsto
    (rawIntegral_hasSum P e v) (Filter.Eventually.of_forall hs)

theorem processTransport_ae (v : Process (E := C) F μ H) :
    processTransport (F := F) (μ := μ) (H := H) v =ᵐ[ν] v := by
  letI : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
  exact Lp.coeFn_compMeasurePreserving _ _

theorem processTransport_stopped (t : ℝ≥0) (v : Process (E := C) F μ H)
    (hv : ∀ᵐ p ∂energyMeasure μ H, t < p.1 → v p = 0) :
    ∀ᵐ p ∂ν, t < p.1 → processTransport (F := F) (μ := μ) (H := H) v p = 0 := by
  let S : Set (ℝ≥0 × Ω) := Set.Ioi t ×ˢ Set.univ
  have hS : MeasurableSet[F.predictable] S :=
    measurableSet_predictable_Ioi_prod MeasurableSet.univ
  have hz : S.indicator (fun p ↦ ‖v p‖) =ᵐ[energyMeasure μ H] fun _ ↦ (0 : ℝ) := by
    filter_upwards [hv] with p hp
    by_cases h : p ∈ S
    · rw [Set.indicator_of_mem h, hp h.1, norm_zero]
    · exact Set.indicator_of_notMem h _
  have htrim := ae_eq_trim_of_measurable (predictable_le_product F)
    ((Lp.stronglyMeasurable v).norm.measurable.indicator hS) measurable_const hz
  have hν : ν = (energyMeasure μ H).trim (predictable_le_product F) :=
    (FilteredScalarIto.processMeasure_eq (𝓖 := F) (μ := μ) H
      (B := fun _ _ ↦ (0 : ℝ)) (fun _ ↦ measurable_const)).symm
  have hle : ae ν ≤ ae ((energyMeasure μ H).trim (predictable_le_product F)) := by rw [hν]
  filter_upwards [processTransport_ae v, htrim.filter_mono hle] with p hp hzero ht
  rw [hp]
  apply norm_eq_zero.mp
  simpa only [Set.indicator_of_mem (show p ∈ S from ⟨ht, Set.mem_univ _⟩)] using hzero

/-- The complete cylindrical terminal isometry, centering and adapted
stopping record from exactly the finite-horizon law used by the paper. -/
def terminalIto (P : FiniteScalarIto.Coordinates F μ H ι) (e : HilbertBasis ι ℝ C) :
    StandardTerminalIto (C := C) (E := ℝ) F μ H where
  integral := integral P e
  centered := integral_centered P e
  adapted t v hv := by
    have ha := rawIntegral_adapted P e t (processTransport v) (processTransport_stopped t v hv)
    exact ⟨ha.mk _, ha.stronglyMeasurable_mk, ha.ae_eq_mk⟩

end SHEStochastic.FiniteCylindricalIto
