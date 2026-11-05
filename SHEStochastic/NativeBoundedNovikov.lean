module

public import SHEStochastic.NativeBoundedExponential
public import SHEStochastic.FiniteCylindricalTerminalIto
public import SHE.StandardTerminalNovikov
public import SHE.ExponentialChangeMeasure

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHEStochastic.NativeBoundedNovikov
open MeasureTheory ProbabilityTheory SHE SHE.PredictableL2
open scoped NNReal ENNReal Topology

variable {Ω C ι : Type*} [MeasurableSpace Ω] [Countable ι] [DecidableEq ι]
  [NormedAddCommGroup C] [InnerProductSpace ℝ C] [CompleteSpace C]
  [MeasurableSpace C] [BorelSpace C] [SecondCountableTopology C]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {H : ℝ≥0}

theorem energy_transport_ae (u : Process (E := C) F μ H) :
    NativeEnergy.energy (FiniteCylindricalIto.processTransport u) =ᵐ[μ]
      StochasticExponential.bracket F μ H u := by
  have hh := NativeEnergy.energy_ae_of_ae _ _ (FiniteCylindricalIto.processTransport_ae u)
  filter_upwards [hh] with ω hω
  change NativeEnergy.energy (FiniteCylindricalIto.processTransport u) ω =
    ∫ r, ‖u (r, ω)‖ ^ 2 ∂timeMeasure H
  rw [timeMeasure_eq]
  exact hω

theorem density_transport_ae (P : FiniteScalarIto.Family F μ H ι)
    (e : HilbertBasis ι ℝ C) (u : Process (E := C) F μ H) :
    NativeExponential.density P e (-1) (FiniteCylindricalIto.processTransport u) =ᵐ[μ]
      StochasticExponential.density F μ H (FiniteCylindricalIto.terminalIto P.toCoordinates e) u := by
  filter_upwards [energy_transport_ae u] with ω hω
  change Real.exp (-1 * FiniteCylindricalIto.rawIntegral P.toCoordinates e
    (FiniteCylindricalIto.processTransport u) ω - (-1 : ℝ) ^ 2 *
      NativeEnergy.energy (FiniteCylindricalIto.processTransport u) ω / 2) = _
  rw [hω]
  simp only [neg_one_mul, neg_one_sq, one_mul]
  rfl

/-- The bounded-energy mean-one result in exactly the manuscript's
original process and density notation. This proves the cap application
of box 6 without assuming the full general Novikov package. -/
theorem mean_one_of_cap (P : FiniteScalarIto.Family F μ H ι) (e : HilbertBasis ι ℝ C)
    (u : Process (E := C) F μ H) (K : ℝ) (hK : 0 ≤ K)
    (hcap : ∀ᵐ ω ∂μ, StochasticExponential.bracket F μ H u ω ≤ K) :
    Integrable (StochasticExponential.density F μ H (FiniteCylindricalIto.terminalIto P.toCoordinates e) u) μ ∧
      (∫ ω, StochasticExponential.density F μ H (FiniteCylindricalIto.terminalIto P.toCoordinates e) u ω ∂μ) = 1 := by
  have hc : ∀ᵐ ω ∂μ, NativeEnergy.energy (FiniteCylindricalIto.processTransport u) ω ≤ K := by
    filter_upwards [energy_transport_ae u, hcap] with ω he hω
    rw [he]
    exact hω
  obtain ⟨hLp, he, _⟩ := NativeBoundedExponential.bounded_energy P e (-1)
    (FiniteCylindricalIto.processTransport u) K hK hc
  have hd := density_transport_ae P e u
  exact ⟨(hLp.integrable (by norm_num)).congr hd, (integral_congr_ae hd.symm).trans he⟩

/-- The actual exponential change of measure is a probability for the
bounded-energy controls used by the uniqueness proof, with no Novikov
axiom among the inputs. -/
theorem probability_of_cap (P : FiniteScalarIto.Family F μ H ι) (e : HilbertBasis ι ℝ C)
    (u : Process (E := C) F μ H) (K : ℝ) (hK : 0 ≤ K)
    (hcap : ∀ᵐ ω ∂μ, StochasticExponential.bracket F μ H u ω ≤ K) :
    IsProbabilityMeasure (ExponentialChangeMeasure.measure μ
      (fun ω ↦ (FiniteCylindricalIto.terminalIto P.toCoordinates e).integral u ω)
      (StochasticExponential.bracket F μ H u)) := by
  obtain ⟨hi, he⟩ := mean_one_of_cap P e u K hK hcap
  exact ExponentialChangeMeasure.probability μ _ _ hi he

end SHEStochastic.NativeBoundedNovikov
