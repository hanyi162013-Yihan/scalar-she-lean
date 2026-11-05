module
public import SHE.CanonicalConditionalBrownianLaw
public import SHE.AllHorizonCylindricalCoordinates
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 2000000
namespace SHE.AllHorizonOriginalConditionalBrownian
open MeasureTheory ProbabilityTheory PredictableL2 Set
open scoped NNReal ENNReal ProbabilityTheory MeasureTheory
variable{Ω P E ι C:Type*}[MeasurableSpace Ω][MeasurableSpace P]
variable[Countable ι][DecidableEq ι]
variable[NormedAddCommGroup E][InnerProductSpace ℝ E][CompleteSpace E]
variable[MeasurableSpace E][BorelSpace E][SecondCountableTopology E]
variable[NormedAddCommGroup C][InnerProductSpace ℝ C]
variable[MeasurableSpace C][BorelSpace C][SecondCountableTopology C]
variable(𝓕:Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ:Measure Ω)[IsProbabilityMeasure μ](H:ℝ≥0)
variable(U:ℝ≥0→Ω→E) (hc:∀ω,Continuous (fun t=>U t ω))
variable(hU:∀t,Measurable[𝓕 t] (U t))
variable(e:ι→C) (he:Orthonormal ℝ e) (J:StandardTerminalIto (C:=C) (E:=ℝ) 𝓕 μ H)
variable(B:ℝ≥0) (hBDG:StandardTerminalBDG16 J B)  (hpos:0<H)
variable(hnull:NullCompleteFiltration.ContainsNullSets 𝓕 μ) (hLevy:StandardTerminalLevy J)

def bundle(v h:ℝ≥0):Ω→CanonicalFutureStateDriver.Space (E:=E) (ι:=ι) h:=
  CanonicalFutureStateDriver.bundle U hc (RawCylindricalCoordinates.continuous 𝓕 μ H e J)
    (fun i=>BoundedStoppedVersion.continuous_version 𝓕 μ H J
      (RawCylindricalCoordinates.row 𝓕 μ H e i) hpos) v h

include he hBDG hpos hnull in
private theorem adapted(i:ι) (t:ℝ≥0):
    Measurable[𝓕 t] (RawCylindricalCoordinates.continuous 𝓕 μ H e J i t):=by
  exact ((show IsStronglyPredictable 𝓕 (RawCylindricalCoordinates.continuous 𝓕 μ H e J i) from
    AllHorizonStoppedVersion.predictable_version 𝓕 μ H J
      (RawCylindricalCoordinates.row 𝓕 μ H e i) hpos hnull B hBDG
      (by norm_num:0≤(1:ℝ)) (RawCylindricalCoordinates.row_norm 𝓕 μ H e he i)).stronglyAdapted t).measurable

include hU he hBDG hpos hnull hLevy in
/-- Direct actual-SAME-J client: no conditional Brownian law or restart
independence is supplied as an additional hypothesis. -/
theorem law(v h:ℝ≥0) (hvh:v+h≤H) (Z:Ω→P) (hZ:Measurable[𝓕 v] Z):
    ∀ᵐp∂μ.map Z,∀n (a:Fin n→ι),
      FiniteBrownianLawOn (CanonicalStateDriverFiltration.filtration (E:=E) (ι:=ι) h)
        (condDistrib (bundle 𝓕 μ H U hc e J hpos v h) Z μ p) h
        (fun i=>CanonicalStateDriverFiltration.coordinate h (a i))
        (fun i j=>if a i=a j then 1 else 0):=by
  exact CanonicalConditionalBrownianLaw.law 𝓕 μ H U hc _ _ hU
    (adapted 𝓕 μ H e he J B hBDG hpos hnull)
    (AllHorizonCylindricalCoordinates.finite_laws 𝓕 μ H e he J B hBDG hpos hnull hLevy)
    v h hvh Z hZ
end SHE.AllHorizonOriginalConditionalBrownian
