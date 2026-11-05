module

public import SHEStochastic.FiniteScalarIto
public import SHEStochastic.ColumnsHilbertSum
public import SHEStochastic.L2HilbertSum

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

/-- Reuse the proved total Hilbert decomposition in predictable L2. -/
def sourceEquiv (e : HilbertBasis ι ℝ C) :
    letI : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
    Lp C 2 ν ≃ₗᵢ[ℝ] lp (fun _ : ι ↦ Lp ℝ 2 ν) 2 := by
  letI : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
  exact (L2HilbertSum.total ν (ColumnsHilbertSum.unit e)
    (ColumnsHilbertSum.unit_total e)).linearIsometryEquiv

variable (P : FiniteScalarIto.Coordinates F μ H ι) (e : HilbertBasis ι ℝ C)

/-- The cylindrical isometry is the Hilbert sum of the actual mutually
orthogonal coordinate integrals, all constructed on the original space. -/
def rawIntegral : Lp C 2 ν →ₗᵢ[ℝ] Lp ℝ 2 μ := by
  letI : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
  exact (FiniteScalarIto.orthogonal P).linearIsometry.comp
    (sourceEquiv (F := F) (μ := μ) (H := H) e).toLinearIsometry

theorem rawIntegral_hasSum (v : Lp C 2 ν) :
    HasSum (fun i ↦ FiniteScalarIto.rawIsometry P i (sourceEquiv e v i)) (rawIntegral P e v) := by
  letI : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
  exact (FiniteScalarIto.orthogonal P).hasSum_linearIsometry (sourceEquiv e v)

theorem sourceEquiv_unit (i : ι) (f : Lp ℝ 2 ν) :
    letI : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
    sourceEquiv (F := F) (μ := μ) (H := H) e
      (L2HilbertSum.lift ν (ColumnsHilbertSum.unit e i) f) = lp.single 2 i f := by
  letI : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
  apply (sourceEquiv (F := F) (μ := μ) (H := H) e).symm.injective
  rw [LinearIsometryEquiv.symm_apply_apply]
  have hs := L2HilbertSum.total ν (ColumnsHilbertSum.unit e) (ColumnsHilbertSum.unit_total e)
  exact (hs.linearIsometryEquiv_symm_apply_single (i := i) f).symm

/-- A scalar basis-coordinate row retains exactly its coordinate integral. -/
theorem rawIntegral_unit (i : ι) (f : Lp ℝ 2 ν) :
    letI : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
    rawIntegral P e (L2HilbertSum.lift ν (ColumnsHilbertSum.unit e i) f) =
      FiniteScalarIto.rawIsometry P i f := by
  letI : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
  change (FiniteScalarIto.orthogonal P).linearIsometry
    (sourceEquiv e (L2HilbertSum.lift ν (ColumnsHilbertSum.unit e i) f)) = _
  rw [sourceEquiv_unit]
  exact (FiniteScalarIto.orthogonal P).linearIsometry_apply_single f

theorem rawIntegral_centered (v : Lp C 2 ν) : ∫ ω, rawIntegral P e v ω ∂μ = 0 := by
  let L := innerSL ℝ (Lp.const 2 μ (1 : ℝ))
  have hs := L.hasSum (rawIntegral_hasSum P e v)
  have hi (i : ι) : L (FiniteScalarIto.rawIsometry P i (sourceEquiv e v i)) = 0 := by
    change inner ℝ (Lp.const 2 μ (1 : ℝ)) (FiniteScalarIto.rawIsometry P i (sourceEquiv e v i)) = 0
    rw [← FiniteScalarIto.mean_eq_inner]
    exact FiniteScalarIto.rawIsometry_centered P i _
  have hz : L (rawIntegral P e v) = 0 := hs.unique
    (by simpa only [hi] using (hasSum_zero : HasSum (fun _ : ι ↦ (0 : ℝ)) 0))
  rw [FiniteScalarIto.mean_eq_inner]
  exact hz

omit P e in
def processTransport : Process (E := C) F μ H →ₗᵢ[ℝ] Lp C 2 ν := by
  letI : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
  exact Lp.compMeasurePreservingₗᵢ ℝ id
    ⟨measurable_id, by
      rw [Measure.map_id]
      exact (FilteredScalarIto.processMeasure_eq (𝓖 := F) (μ := μ) H
        (B := fun _ _ ↦ (0 : ℝ)) (fun _ ↦ measurable_const)).symm⟩

/-- The native-horizon cylindrical predictable-L2 integral isometry.
The adapted stopping field is assembled separately; this definition
does not yet claim the complete StandardTerminalIto record. -/
def integral : Process (E := C) F μ H →ₗᵢ[ℝ] Lp ℝ 2 μ :=
  (rawIntegral P e).comp (processTransport (F := F) (μ := μ) (H := H))

theorem integral_centered (v : Process (E := C) F μ H) : ∫ ω, integral P e v ω ∂μ = 0 :=
  rawIntegral_centered P e _

end SHEStochastic.FiniteCylindricalIto
