module
public import SHE.NativeFourierSections
@[expose] public section
noncomputable section
set_option autoImplicit false
namespace SHE.SpatialVersionFourier
open MeasureTheory StoppedFourier
local instance spatialVersionFourier_period : Fact (0<2*Real.pi):=⟨by positivity⟩
variable {Ω:Type*}[MeasurableSpace Ω](μ:Measure Ω)[SFinite μ]

/-- Joint scalar versions with the SAME spatial sections have equal
Fourier coefficients on one sample event, by ordinary measurable
equality-event Fubini. -/
theorem coefficients {Y Z:HeatCircle×Ω→ℝ}(hY:Measurable Y)(hZ:Measurable Z)
    (he:∀ᵐx:HeatCircle∂AddCircle.haarAddCircle,(fun ω=>Y (x,ω))=ᵐ[μ] fun ω=>Z (x,ω)):
    ∀ᵐω∂μ,∀l:ℤ,fourierCoeff (fun x:HeatCircle=>(Y (x,ω):ℂ)) l=
      fourierCoeff (fun x:HeatCircle=>(Z (x,ω):ℂ)) l:=by
  have hs:MeasurableSet {z:HeatCircle×Ω|Y z=Z z}:=measurableSet_eq_fun hY hZ
  have hcomm:∀ᵐω∂μ,∀ᵐx:HeatCircle∂AddCircle.haarAddCircle,Y (x,ω)=Z (x,ω):=
    (Measure.ae_ae_comm hs).mp he
  filter_upwards [hcomm] with ω hω
  intro l
  exact congrFun (fourierCoeff_congr_ae (hω.mono (fun x hx=>congrArg Complex.ofReal hx))) l
end SHE.SpatialVersionFourier
