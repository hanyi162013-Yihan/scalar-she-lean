module

public import SHEStochastic.FiniteCoordinateIdentity
public import SHEStochastic.FiniteCylindricalParameterVersions
public import SHE.RawCylindricalCoordinates

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section

namespace SHEStochastic.FiniteCylindricalIto
open MeasureTheory SHE SHE.PredictableL2
open scoped NNReal ENNReal
variable {Ω ι C : Type*} [MeasurableSpace Ω] [Countable ι] [DecidableEq ι]
  [NormedAddCommGroup C] [InnerProductSpace ℝ C] [CompleteSpace C]
  [MeasurableSpace C] [BorelSpace C] [SecondCountableTopology C]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {μ : Measure Ω} [IsProbabilityMeasure μ] {H : ℝ≥0}
local notation "ν" => FiniteScalarIto.inputMeasure F μ H

theorem constantRow_trim_ae (e : HilbertBasis ι ℝ C) (i : ι) :
    RawCylindricalCoordinates.row F μ H (e : ι → C) i =ᵐ[ν] fun _ ↦ e i := by
  have h := (RotatedCylindricalCoordinates.constant_memLp F μ H (e i)).coeFn_toLp
  have hle : ae ν ≤ ae ((energyMeasure μ H).trim (predictable_le_product F)) := by
    rw [FilteredScalarIto.processMeasure_eq (𝓖 := F) (μ := μ) H
      (B := fun _ _ ↦ (0 : ℝ)) (fun _ ↦ measurable_const)]
    exact le_rfl
  exact h.filter_mono hle

theorem oneStep_embedding_ae (t : ℝ≥0) (ht : t ≤ H) :
    FiniteScalarIto.embedding F μ H (FiniteScalarIto.oneStep F H t ht) =ᵐ[ν]
      (Set.Ioc 0 t ×ˢ (Set.univ : Set Ω)).indicator (fun _ ↦ (1 : ℝ)) := by
  have h := (FilteredItoCLM.memLp_uncurry_trim_T (𝓖 := F) (μ := μ) H
    (B := fun _ _ ↦ (0 : ℝ)) (fun _ ↦ measurable_const)
    (FiniteScalarIto.oneStep F H t ht).val).coeFn_toLp
  have he := FilteredItoCLM.uncurry_iocSP_T_eq (𝓖 := F)
    (B := fun _ _ ↦ (0 : ℝ)) (fun _ ↦ measurable_const)
    (show (0 : ℝ≥0) ≤ t from zero_le) ht
    (MeasurableSet.univ : MeasurableSet[F 0] (Set.univ : Set Ω))
  filter_upwards [h] with p hp
  exact hp.trans (congrFun he p)

/-- The literal manuscript coordinate row is the elementary basis input,
after identifying strict-before and closed-right time conventions. -/
theorem coordinate_source (e : HilbertBasis ι ℝ C) (i : ι) (t : ℝ≥0) (ht : t ≤ H) :
    letI : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
    processTransport (StoppedItoInputs.stop F μ H t
      (RawCylindricalCoordinates.row F μ H (e : ι → C) i)) =
      L2HilbertSum.lift ν (ColumnsHilbertSum.unit e i)
        (FiniteScalarIto.embedding F μ H (FiniteScalarIto.oneStep F H t ht)) := by
  letI : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
  apply Lp.ext
  let row := RawCylindricalCoordinates.row F μ H (e : ι → C) i
  filter_upwards [processTransport_stop_ae t row, processTransport_ae row,
    constantRow_trim_ae e i, oneStep_embedding_ae t ht,
    L2HilbertSum.lift_ae ν (ColumnsHilbertSum.unit e i)
      (FiniteScalarIto.embedding F μ H (FiniteScalarIto.oneStep F H t ht)),
    FilteredItoCLM.ae_fst_mem_Ioc_trimMeasure_T (𝓖 := F) (μ := μ) H
      (B := fun _ _ ↦ (0 : ℝ)) (fun _ ↦ measurable_const),
    FilteredScalarIto.trim_ae_fst_ne (𝓖 := F) (μ := μ) H t
      (B := fun _ _ ↦ (0 : ℝ)) (fun _ ↦ measurable_const)] with p hs htr hr hb hu hm hn
  rw [hs, hu, hb]
  by_cases hp : p.1 < t
  · have hbefore : p ∈ StoppedItoInputs.before (Ω := Ω) t := by
      change (p.1 : ℝ) < (t : ℝ); exact_mod_cast hp
    have hband : p ∈ Set.Ioc 0 t ×ˢ (Set.univ : Set Ω) := ⟨⟨hm.1, hp.le⟩, Set.mem_univ _⟩
    rw [Set.indicator_of_mem hbefore, htr, hr, Set.indicator_of_mem hband]
    simp [ColumnsHilbertSum.unit, LinearIsometry.toSpanSingleton_apply]
  · have hbefore : p ∉ StoppedItoInputs.before (Ω := Ω) t := by
      change ¬ (p.1 : ℝ) < (t : ℝ); exact_mod_cast hp
    have hband : p ∉ Set.Ioc 0 t ×ˢ (Set.univ : Set Ω) :=
      fun h ↦ hp (lt_of_le_of_ne h.1.2 hn)
    rw [Set.indicator_of_notMem hbefore, Set.indicator_of_notMem hband, map_zero]

/-- Exact driver-coordinate field of the original Brownian construction
interface: the selected integral produces the given W, not merely a
process with the same Gaussian distributions. -/
theorem coordinate_integral (P : FiniteScalarIto.Family F μ H ι) (e : HilbertBasis ι ℝ C)
    (i : ι) (t : ℝ≥0) (ht : t ≤ H) :
    (terminalIto P.toCoordinates e).integral (StoppedItoInputs.stop F μ H t
      (RawCylindricalCoordinates.row F μ H (e : ι → C) i)) =ᵐ[μ] P.W i t := by
  letI : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
  change rawIntegral P.toCoordinates e (processTransport _) =ᵐ[μ] _
  rw [coordinate_source e i t ht]
  exact rawIntegral_oneStep P.toCoordinates e i t ht

end SHEStochastic.FiniteCylindricalIto
