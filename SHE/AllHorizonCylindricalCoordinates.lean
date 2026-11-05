module
public import SHE.RotatedCylindricalBrownian
public import SHE.StoppedInputAlgebra
public import SHE.AllHorizonStoppedVersion
public import SHE.RawCylindricalCoordinates
public import SHE.FiniteCoordinateLaw
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1400000
namespace SHE.AllHorizonCylindricalCoordinates
open MeasureTheory ProbabilityTheory PredictableL2 StoppedItoInputs Set
open scoped NNReal ENNReal
variable {Ω C ι:Type*}[MeasurableSpace Ω]
variable [NormedAddCommGroup C][InnerProductSpace ℝ C][MeasurableSpace C][BorelSpace C][SecondCountableTopology C]
variable[Countable ι][DecidableEq ι]
variable(𝓕:Filtration ℝ≥0 ‹MeasurableSpace Ω›)(μ:Measure Ω)[IsProbabilityMeasure μ](H:ℝ≥0)
variable(e:ι→C)(he:Orthonormal ℝ e)
variable(J:StandardTerminalIto (C:=C) (E:=ℝ) 𝓕 μ H)

open RawCylindricalCoordinates
variable(B:ℝ≥0)(hBDG:StandardTerminalBDG16 J B)(hpos:0<H)
variable(hnull:NullCompleteFiltration.ContainsNullSets 𝓕 μ)

abbrev continuous:=RawCylindricalCoordinates.continuous 𝓕 μ H e J

include he hBDG hpos in
theorem continuous_ae(i:ι)(t:ℝ≥0):continuous 𝓕 μ H e J i t=ᵐ[μ] value 𝓕 μ H e J i t:=by
  have hh:=AllHorizonStoppedVersion.version_ae 𝓕 μ H J (row 𝓕 μ H e i) hpos B hBDG
    (by norm_num:0≤(1:ℝ)) (row_norm 𝓕 μ H e he i) t
  rw [stop_min] at hh
  exact hh

include he hBDG hpos hnull in
theorem finite_laws(hLevy:StandardTerminalLevy J)(n:ℕ)(a:Fin n→ι):
    FiniteBrownianLawOn 𝓕 μ H (fun i=>continuous 𝓕 μ H e J (a i))
      (fun i j=>if a i=a j then 1 else 0):=by
  apply hLevy n (fun i=>row 𝓕 μ H e (a i))
  · intro i
    exact AllHorizonStoppedVersion.predictable_version 𝓕 μ H J (row 𝓕 μ H e (a i)) hpos hnull B hBDG
      (by norm_num:0≤(1:ℝ)) (row_norm 𝓕 μ H e he (a i))
  · intro i ω
    exact BoundedStoppedVersion.continuous_version 𝓕 μ H J (row 𝓕 μ H e (a i)) hpos ω
  · intro t ht
    filter_upwards [ae_all_iff.mpr (fun i:Fin n=>continuous_ae 𝓕 μ H e he J B hBDG hpos (a i) t)] with ω hω i
    exact hω i
  · filter_upwards [ae_all_iff.mpr (fun i:Fin n=>RotatedCylindricalCoordinates.constant_ae 𝓕 μ H (e (a i)))] with p hp i j
    change inner ℝ (RotatedCylindricalCoordinates.constant 𝓕 μ H (e (a i)) p)
      (RotatedCylindricalCoordinates.constant 𝓕 μ H (e (a j)) p)=_
    rw [hp i,hp j]
    exact orthonormal_iff_ite.mp he (a i) (a j)

end SHE.AllHorizonCylindricalCoordinates
