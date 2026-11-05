module

public import SHEStochastic.NativeBandMoments
public import SHEStochastic.FiniteItoStoppedVersions

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHEStochastic.NativeBoundedMoments
open MeasureTheory ProbabilityTheory SHE SHE.PredictableL2 SHE.StoppedItoInputs
open scoped NNReal ENNReal

variable {Ω C ι : Type*} [MeasurableSpace Ω] [Countable ι] [DecidableEq ι]
  [NormedAddCommGroup C] [InnerProductSpace ℝ C] [CompleteSpace C]
  [MeasurableSpace C] [BorelSpace C] [SecondCountableTopology C]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {H : ℝ≥0}

/-- Finite moments for bounded rows follow from the existing native
sub-Gaussian estimate, without assuming any BDG inequality. -/
theorem subgaussian_stopped (P : FiniteScalarIto.Family F μ H ι) (e : HilbertBasis ι ℝ C)
    (u : Process (E := C) F μ H) (M : ℝ≥0)
    (hu : ∀ᵐ p ∂(energyMeasure μ H).trim (predictable_le_product F), ‖u p‖ ≤ M)
    (t : ℝ≥0) (ht : t ≤ H) :
    HasSubgaussianMGF
      ((FiniteCylindricalIto.terminalIto P.toCoordinates e).integral (stop F μ H t u) : Ω → ℝ)
      (t * M ^ 2) μ := by
  have hnat : ∀ᵐ p ∂FiniteScalarIto.inputMeasure F μ H, ‖u p‖ ≤ M := by
    rw [NativeRowRepresentatives.inputMeasure_eq]
    exact hu
  have hh := NativeBandMoments.increment_subgaussian P e u M hnat
    (s := 0) (t := t) zero_le ht
  simp only [tsub_zero, NNReal.coe_zero] at hh
  apply hh.congr
  have hz : (FiniteCylindricalIto.terminalIto P.toCoordinates e).integral (stop F μ H 0 u) =ᵐ[μ]
      (fun _ ↦ (0 : ℝ)) := by
    rw [stop_zero, map_zero]
    exact Lp.coeFn_zero _ _ _
  filter_upwards [hz] with ω hω
  change _ - _ = _
  rw [hω, sub_zero]

theorem memLp_stopped (P : FiniteScalarIto.Family F μ H ι) (e : HilbertBasis ι ℝ C)
    (u : Process (E := C) F μ H) (M : ℝ≥0)
    (hu : ∀ᵐ p ∂(energyMeasure μ H).trim (predictable_le_product F), ‖u p‖ ≤ M)
    (t : ℝ≥0) (p : ℝ≥0) :
    MemLp ((FiniteCylindricalIto.terminalIto P.toCoordinates e).integral (stop F μ H t u)) p μ := by
  by_cases ht : t ≤ H
  · exact (subgaussian_stopped P e u M hu t ht).memLp p
  · have hHt : H ≤ t := le_of_not_ge ht
    have he : stop F μ H t u = stop F μ H H u := by
      calc
        _ = stop F μ H t (stop F μ H H u) := by rw [FiniteItoStoppedVersions.stop_horizon]
        _ = _ := by
          rw [StoppedInputAlgebra.stop_stop, min_eq_right (show (H : ℝ) ≤ t by exact_mod_cast hHt)]
    rw [he]
    exact (subgaussian_stopped P e u M hu H le_rfl).memLp p

end SHEStochastic.NativeBoundedMoments
