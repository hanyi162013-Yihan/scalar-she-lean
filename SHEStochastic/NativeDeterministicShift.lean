module

public import SHEStochastic.NativeIntegralUniqueness
public import SHEStochastic.NativeBrownianCoordinates
public import SHEStochastic.FiniteCylindricalLocality
public import SHE.DeterministicItoShiftCoordinates
public import SHE.DeterministicItoShiftLocality

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1300000
noncomputable section

namespace SHEStochastic.NativeDeterministicShift
open MeasureTheory SHE SHE.PredictableL2
open scoped NNReal ENNReal
variable {Ω C ι : Type*} [MeasurableSpace Ω] [Countable ι] [DecidableEq ι]
  [NormedAddCommGroup C] [InnerProductSpace ℝ C] [CompleteSpace C]
  [MeasurableSpace C] [BorelSpace C] [SecondCountableTopology C]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {H v h : ℝ≥0} (hvh : v+h≤H)
  (P : FiniteScalarIto.Family F μ H ι)
  (Q : FiniteScalarIto.Family (DeterministicItoShift.filtration F v) μ h ι)
  (e : HilbertBasis ι ℝ C)
  (hW : ∀ i t,t≤h → Q.W i t =ᵐ[μ] fun ω => P.W i (v+t) ω-P.W i v ω)

include hW in
/-- The native local Brownian integral is the original native global
integral applied to its literal deterministic window extension. This
follows from ordinary locality and the same coordinate increments. -/
theorem integral_ae (u : Process (E := C) (DeterministicItoShift.filtration F v) μ h) :
    (FiniteCylindricalIto.terminalIto Q.toCoordinates e).integral u=
      (FiniteCylindricalIto.terminalIto P.toCoordinates e).integral
        (DeterministicItoShift.input F μ H v h hvh u) := by
  let J := FiniteCylindricalIto.terminalIto P.toCoordinates e
  let K := DeterministicItoShift.integral F μ H v h hvh J
  have hc (i : ι) (t : ℝ≥0) (ht : t≤h) :
      RawCylindricalCoordinates.value (DeterministicItoShift.filtration F v) μ h (e : ι → C) K i t =ᵐ[μ] Q.W i t := by
    have hs := DeterministicItoShiftCoordinates.value F μ H v h hvh (e : ι → C) J i t ht
    have hp1 := FiniteCylindricalIto.coordinate_integral P e i (v+t) ((add_le_add le_rfl ht).trans hvh)
    have hp0 := FiniteCylindricalIto.coordinate_integral P e i v ((le_add_of_nonneg_right (show 0≤h from bot_le)).trans hvh)
    exact (hs.trans (hp1.sub hp0)).trans (hW i t ht).symm
  have hl : StandardTerminalPastLocality K :=
    DeterministicItoShift.locality F μ H v h hvh J (FiniteCylindricalIto.pastLocality P e)
  exact (NativeIntegralUniqueness.integral Q e K hl hc u).symm

/-- The pointwise driver identity is a specialization of the version
invariant deterministic-window theorem. -/
theorem integral
    (hW : ∀ i t,t≤h → Q.W i t=fun ω => P.W i (v+t) ω-P.W i v ω)
    (u : Process (E := C) (DeterministicItoShift.filtration F v) μ h) :
    (FiniteCylindricalIto.terminalIto Q.toCoordinates e).integral u=
      (FiniteCylindricalIto.terminalIto P.toCoordinates e).integral
        (DeterministicItoShift.input F μ H v h hvh u) :=
  integral_ae hvh P Q e (fun i t ht => Filter.Eventually.of_forall (congrFun (hW i t ht))) u

end SHEStochastic.NativeDeterministicShift
