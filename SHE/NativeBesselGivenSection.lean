module
public import SHE.NativeBesselFieldAE
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace SHE.NativeBesselGivenSection
open MeasureTheory StoppedFourier AddCircle
open scoped ENNReal
local instance : Fact (0<2*Real.pi):=⟨by positivity⟩
local instance : MeasurableSpace CircleL2:=borel _
local instance : BorelSpace CircleL2:=⟨rfl⟩
local instance : SecondCountableTopology CircleL2:=
  (_root_.fourierBasis (T:=2*Real.pi)).repr.toHomeomorph.secondCountableTopology
variable {P:Type*}[MeasurableSpace P]

/-- A literal Borel scalar representative of a supplied actual L2
section has exactly its native multiplier, at every parameter point. -/
theorem value_eq(Λ ρ:ℝ)(hΛ:1≤Λ)(hρ:0≤ρ)(F:P×HeatCircle→ℂ)(hF:Measurable F)
    (A:P→CircleL2)(p:P)(he:(fun x=>F (p,x))=ᵐ[haarAddCircle] A p):
    NativeBesselFieldAE.value Λ ρ hΛ hρ F p=OneInputOperator.besselHalf Λ ρ hΛ hρ (A p):=by
  have hm:MemLp (fun x=>F (p,x)) 2 haarAddCircle:=
    (memLp_congr_ae he).mpr (Lp.memLp (A p))
  have ha:=MeasurableL2FieldAE.realization_ae haarAddCircle F hF p
    ((MeasurableL2FieldAE.section_memLp_iff haarAddCircle F hF p).mp hm)
  have hreal:MeasurableL2FieldAE.realization haarAddCircle F p=A p:=Lp.ext (ha.trans he)
  unfold NativeBesselFieldAE.value
  rw [hreal]
end SHE.NativeBesselGivenSection
