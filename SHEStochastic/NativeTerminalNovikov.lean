module

public import SHEStochastic.NativeNovikov
public import SHEStochastic.NativeBoundedNovikov

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHEStochastic.NativeTerminalNovikov
open MeasureTheory ProbabilityTheory SHE SHE.PredictableL2
open scoped NNReal ENNReal

variable {Ω C ι : Type*} [MeasurableSpace Ω] [Countable ι] [DecidableEq ι]
  [NormedAddCommGroup C] [InnerProductSpace ℝ C] [CompleteSpace C]
  [MeasurableSpace C] [BorelSpace C] [SecondCountableTopology C]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {H : ℝ≥0}

/-- The exact old external package 6 for the selected native cylindrical
integral. The hypothesis is only Novikov's exponential-energy condition. -/
theorem standardTerminalNovikov (P : FiniteScalarIto.Family F μ H ι) (e : HilbertBasis ι ℝ C) :
    StandardTerminalNovikov (FiniteCylindricalIto.terminalIto P.toCoordinates e) := by
  intro u hNov
  have hE := NativeBoundedNovikov.energy_transport_ae u
  have he : (fun ω ↦ Real.exp ((-1 : ℝ) ^ 2 *
      NativeEnergy.energy (FiniteCylindricalIto.processTransport u) ω / 2)) =ᵐ[μ]
      (fun ω ↦ Real.exp (StochasticExponential.bracket F μ H u ω / 2)) := by
    filter_upwards [hE] with ω hω
    change Real.exp ((-1 : ℝ) ^ 2 *
      NativeEnergy.energy (FiniteCylindricalIto.processTransport u) ω / 2) = _
    rw [hω, neg_one_sq, one_mul]
  obtain ⟨hi, hmean⟩ := NativeNovikov.mean_one P e (-1)
    (FiniteCylindricalIto.processTransport u) (hNov.congr he.symm)
  have hd := NativeBoundedNovikov.density_transport_ae P e u
  exact ⟨hi.congr hd, (integral_congr_ae hd.symm).trans hmean⟩

end SHEStochastic.NativeTerminalNovikov
