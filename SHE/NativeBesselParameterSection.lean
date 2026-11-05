module
public import SHE.NativeBesselFieldAE
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace SHE.NativeBesselParameterSection
open MeasureTheory StoppedFourier AddCircle
open scoped ENNReal
local instance : Fact (0<2*Real.pi):=⟨by positivity⟩
local instance : MeasurableSpace CircleL2:=borel _
local instance : BorelSpace CircleL2:=⟨rfl⟩
variable {P Q:Type*}[MeasurableSpace P][MeasurableSpace Q]

/-- Native realization depends only on the actual spatial section,
even when two Borel parameterizations use different parameter types. -/
theorem congr (Λ ρ:ℝ)(hΛ:1≤Λ)(hρ:0≤ρ)
    (F:P×HeatCircle→ℂ)(G:Q×HeatCircle→ℂ)(p:P)(q:Q)
    (he:(fun x=>F (p,x))=(fun x=>G (q,x))):
    NativeBesselFieldAE.value Λ ρ hΛ hρ F p=NativeBesselFieldAE.value Λ ρ hΛ hρ G q:=by
  have hm:MeasurableL2FieldAE.squareMass haarAddCircle F p=
      MeasurableL2FieldAE.squareMass haarAddCircle G q:=
    congrArg (fun f:HeatCircle→ℂ=>∫⁻x,ENNReal.ofReal (‖f x‖^2) ∂haarAddCircle) he
  have hc:(fun x=>MeasurableL2FieldAE.clean haarAddCircle F (p,x))=
      (fun x=>MeasurableL2FieldAE.clean haarAddCircle G (q,x)):=by
    funext x
    simp only [MeasurableL2FieldAE.clean,hm]
    split_ifs
    · exact congrFun he x
    · rfl
  classical
  let realize:(HeatCircle→ℂ)→CircleL2:=fun f=>
    if h:MemLp f 2 haarAddCircle then h.toLp f else 0
  change OneInputOperator.besselHalf Λ ρ hΛ hρ
      (realize (fun x=>MeasurableL2FieldAE.clean haarAddCircle F (p,x)))=
    OneInputOperator.besselHalf Λ ρ hΛ hρ
      (realize (fun x=>MeasurableL2FieldAE.clean haarAddCircle G (q,x)))
  rw [hc]
end SHE.NativeBesselParameterSection
