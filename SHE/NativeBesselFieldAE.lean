module
public import SHE.MeasurableL2FieldAE
public import SHE.NativeFourierSections
public import SHE.NativeBesselReal
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
namespace SHE.NativeBesselFieldAE
open MeasureTheory AddCircle StoppedFourier
open scoped ENNReal
local instance : Fact (0<2*Real.pi):=⟨by positivity⟩
local instance : MeasurableSpace CircleL2:=borel _
local instance : BorelSpace CircleL2:=⟨rfl⟩
local instance : SecondCountableTopology CircleL2:=
  (_root_.fourierBasis (T:=2*Real.pi)).repr.toHomeomorph.secondCountableTopology
variable {P:Type*}[MeasurableSpace P]
variable (Λ ρ:ℝ)(hΛ:1≤Λ)(hρ:0≤ρ)

def value (F:P×HeatCircle→ℂ)(p:P):CircleL2:=
  OneInputOperator.besselHalf Λ ρ hΛ hρ
    (MeasurableL2FieldAE.realization haarAddCircle F p)

/-- A joint scalar field with AE square sections has an actual Borel
native Bessel-smoothed spatial Hilbert realization. -/
theorem measurable (F:P×HeatCircle→ℂ)(hF:Measurable F):
    Measurable (value Λ ρ hΛ hρ F):=
  (OneInputOperator.besselHalf Λ ρ hΛ hρ).continuous.measurable.comp
    (MeasurableL2FieldAE.realization_measurable haarAddCircle F hF)

theorem coefficients (F:P×HeatCircle→ℂ)(hF:Measurable F)(p:P)
    (hp:MeasurableL2FieldAE.squareMass haarAddCircle F p<∞)(l:ℤ):
    fourierCoeff (value Λ ρ hΛ hρ F p) l=
      (((Λ+(l:ℝ)^2)^(-ρ/2):ℝ):ℂ)*fourierCoeff (fun x=>F (p,x)) l:=by
  rw [value,OneInputOperator.besselHalf_fourierCoeff]
  rw [fourierCoeff_congr_ae (MeasurableL2FieldAE.realization_ae haarAddCircle F hF p hp)]

/-- Any previously identified physical output equals the canonical Borel
Hilbert version; the conclusion is an object identity on the original
parameter measure, with no new joint-version assumption. -/
theorem identified_ae (η:Measure P)(F:P×HeatCircle→ℂ)(hF:Measurable F)
    (hE:(∫⁻p,MeasurableL2FieldAE.squareMass haarAddCircle F p ∂η)<∞)
    (Z:P→CircleL2)
    (hZ:∀ᵐp∂η,∀l:ℤ,fourierCoeff (Z p) l=
      (((Λ+(l:ℝ)^2)^(-ρ/2):ℝ):ℂ)*fourierCoeff (fun x=>F (p,x)) l):
    value Λ ρ hΛ hρ F=ᵐ[η] Z:=by
  filter_upwards [MeasurableL2FieldAE.good_ae haarAddCircle η F hF hE,hZ] with p hp hz
  apply (fourierBasis (T:=2*Real.pi)).repr.injective
  apply lp.ext
  funext l
  simp only [fourierBasis_repr,coefficients Λ ρ hΛ hρ F hF p hp,hz]

theorem energy_ae (η:Measure P)(F:P×HeatCircle→ℂ)(hF:Measurable F)
    (hE:(∫⁻p,MeasurableL2FieldAE.squareMass haarAddCircle F p ∂η)<∞):
    ∀ᵐp∂η,
      Summable (fun l:ℤ=>(Λ+(l:ℝ)^2)^(-ρ)*‖fourierCoeff (fun x=>F (p,x)) l‖^2) ∧
      (∑'l:ℤ,(Λ+(l:ℝ)^2)^(-ρ)*‖fourierCoeff (fun x=>F (p,x)) l‖^2)=‖value Λ ρ hΛ hρ F p‖^2:=by
  filter_upwards [MeasurableL2FieldAE.good_ae haarAddCircle η F hF hE] with p hp
  exact NativeFourierAverage.energy_of_identified Λ ρ hΛ (value Λ ρ hΛ hρ F p)
    (fun x=>F (p,x)) (coefficients Λ ρ hΛ hρ F hF p hp)
end SHE.NativeBesselFieldAE
