module

public import SHEStochastic.NativeGirsanovVector
public import SHEStochastic.NativeBoundedNovikov
public import SHEStochastic.NativeStoppedGram
public import SHE.StandardTerminalGirsanov

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHEStochastic.NativeGirsanovRows
open MeasureTheory ProbabilityTheory SHE SHE.PredictableL2 SHE.StoppedItoInputs SHE.PastItoInputs
open NativeRowRepresentatives NativeStoppedGram
open scoped NNReal ENNReal

variable {Ω C ι : Type*} [MeasurableSpace Ω] [Countable ι] [DecidableEq ι]
  [NormedAddCommGroup C] [InnerProductSpace ℝ C] [CompleteSpace C]
  [MeasurableSpace C] [BorelSpace C] [SecondCountableTopology C]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {H : ℝ≥0}

local notation "νin" => FiniteScalarIto.inputMeasure F μ H
local notation "νt" => MathFin.ItoIntegralCLM.timeMeasure_T H

theorem measure_transport (P : FiniteScalarIto.Family F μ H ι) (e : HilbertBasis ι ℝ C)
    (u : Process (E := C) F μ H) :
    NativeGirsanovTilt.measure P e (FiniteCylindricalIto.processTransport u) =
      ExponentialChangeMeasure.measure μ
        (fun ω ↦ (FiniteCylindricalIto.terminalIto P.toCoordinates e).integral u ω)
        (StochasticExponential.bracket F μ H u) := by
  unfold NativeGirsanovTilt.measure ExponentialChangeMeasure.measure
  apply withDensity_congr_ae
  filter_upwards [NativeBoundedNovikov.density_transport_ae P e u] with ω hω
  change ENNReal.ofReal (NativeExponential.density P e (-1) (FiniteCylindricalIto.processTransport u) ω) = _
  rw [hω]
  rfl

theorem cross_stopped (u R : Process (E := C) F μ H) (t : ℝ≥0) (htH : t ≤ H) :
    NativeCrossEnergy.cross (FiniteCylindricalIto.processTransport (stop F μ H t R))
      (FiniteCylindricalIto.processTransport u) =ᵐ[μ]
      (fun ω ↦ ∫ r, inner ℝ (R (r, ω)) (u (r, ω)) ∂timeMeasure (min t H)) := by
  have hinner : (fun p ↦ inner ℝ
      (FiniteCylindricalIto.processTransport (stop F μ H t R) p)
      (FiniteCylindricalIto.processTransport u p)) =ᵐ[νin]
      (fun p ↦ (Set.Iio t).indicator (fun r ↦ inner ℝ (R (r, p.2)) (u (r, p.2))) p.1) := by
    filter_upwards [stop_transport_ae t R, FiniteCylindricalIto.processTransport_ae u] with p hR hu
    rw [hR, hu]
    by_cases hp : p.1 < t <;> simp [Set.indicator_apply, Set.mem_Iio, hp]
  have hp := ae_eq_of_ae_eq_trim (hm := F.predictable_le_prod) hinner
  have hs := (Measure.measurePreserving_swap (μ := μ)
    (ν := MathFin.ItoIntegralCLM.timeMeasure_T H)).quasiMeasurePreserving.ae hp
  filter_upwards [Measure.ae_ae_of_ae_prod hs] with ω hω
  change (∫ r, inner ℝ
    (FiniteCylindricalIto.processTransport (stop F μ H t R) (r, ω))
    (FiniteCylindricalIto.processTransport u (r, ω)) ∂νt) = _
  calc
    _ = ∫ r, (Set.Iio t).indicator (fun r ↦ inner ℝ (R (r, ω)) (u (r, ω))) r ∂νt :=
      integral_congr_ae hω
    _ = _ := by rw [NativeClockIntegral.before H t htH, min_eq_left htH, timeMeasure_eq]

theorem shift_stopped (P : FiniteScalarIto.Family F μ H ι) (e : HilbertBasis ι ℝ C)
    (u R : Process (E := C) F μ H) (X : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (htH : t ≤ H)
    (hsame : X t =ᵐ[μ] (FiniteCylindricalIto.terminalIto P.toCoordinates e).integral (stop F μ H t R)) :
    girsanovShift u R X t =ᵐ[μ] NativeGirsanovTilt.shift P e (FiniteCylindricalIto.processTransport u)
      (FiniteCylindricalIto.processTransport (stop F μ H t R)) := by
  filter_upwards [hsame, cross_stopped u R t htH] with ω hX hc
  change X t ω + (∫ r, inner ℝ (R (r, ω)) (u (r, ω)) ∂timeMeasure (min t H)) = _
  rw [hX, ← hc]
  rfl

theorem shift_sub (P : FiniteScalarIto.Family F μ H ι) (e : HilbertBasis ι ℝ C)
    (u v w : Lp C 2 νin) :
    NativeGirsanovTilt.shift P e u (v - w) =ᵐ[μ]
      (fun ω ↦ NativeGirsanovTilt.shift P e u v ω - NativeGirsanovTilt.shift P e u w ω) := by
  letI : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
  have hI : (FiniteCylindricalIto.rawIntegral P.toCoordinates e (v - w) : Ω → ℝ) =ᵐ[μ]
      (fun ω ↦ FiniteCylindricalIto.rawIntegral P.toCoordinates e v ω - FiniteCylindricalIto.rawIntegral P.toCoordinates e w ω) := by
    rw [map_sub]
    exact Lp.coeFn_sub _ _
  filter_upwards [hI, NativeCrossEnergy.cross_sub v w u] with ω hIω hc
  change FiniteCylindricalIto.rawIntegral P.toCoordinates e (v - w) ω + NativeCrossEnergy.cross (v - w) u ω =
    (FiniteCylindricalIto.rawIntegral P.toCoordinates e v ω + NativeCrossEnergy.cross v u ω) -
      (FiniteCylindricalIto.rawIntegral P.toCoordinates e w ω + NativeCrossEnergy.cross w u ω)
  rw [hIω, hc]
  ring

end SHEStochastic.NativeGirsanovRows
