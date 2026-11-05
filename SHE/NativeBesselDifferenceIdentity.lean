module
public import SHE.NativeBesselFieldAE
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace SHE.NativeBesselDifferenceIdentity
open MeasureTheory AddCircle StoppedFourier
open scoped ENNReal
local instance : Fact (0<2*Real.pi):=⟨by positivity⟩
local instance : MeasurableSpace CircleL2:=borel _
local instance : BorelSpace CircleL2:=⟨rfl⟩
local instance : SecondCountableTopology CircleL2:=
  (_root_.fourierBasis (T:=2*Real.pi)).repr.toHomeomorph.secondCountableTopology
variable {P:Type*}[MeasurableSpace P]

/-- Literal scalar differences pass to actual native Hilbert versions
after their L2 applicability is established. -/
theorem sub (Λ ρ:ℝ)(hΛ:1≤Λ)(hρ:0≤ρ)
    (F G K:P×HeatCircle→ℂ)(hF:Measurable F)(hG:Measurable G)(hK:Measurable K)
    (p:P)(hpF:MemLp (fun x=>F (p,x)) 2 haarAddCircle)
    (hpG:MemLp (fun x=>G (p,x)) 2 haarAddCircle)
    (hpK:MemLp (fun x=>K (p,x)) 2 haarAddCircle)
    (he:∀ᵐx∂haarAddCircle,F (p,x)=G (p,x)-K (p,x)):
    NativeBesselFieldAE.value Λ ρ hΛ hρ F p=
      NativeBesselFieldAE.value Λ ρ hΛ hρ G p-NativeBesselFieldAE.value Λ ρ hΛ hρ K p:=by
  let A:=MeasurableL2FieldAE.realization haarAddCircle F p
  let B:=MeasurableL2FieldAE.realization haarAddCircle G p
  let C:=MeasurableL2FieldAE.realization haarAddCircle K p
  have ha:A=ᵐ[haarAddCircle] (fun x=>F (p,x)):=
    MeasurableL2FieldAE.realization_ae haarAddCircle F hF p
      ((MeasurableL2FieldAE.section_memLp_iff haarAddCircle F hF p).mp hpF)
  have hb:B=ᵐ[haarAddCircle] (fun x=>G (p,x)):=
    MeasurableL2FieldAE.realization_ae haarAddCircle G hG p
      ((MeasurableL2FieldAE.section_memLp_iff haarAddCircle G hG p).mp hpG)
  have hc:C=ᵐ[haarAddCircle] (fun x=>K (p,x)):=
    MeasurableL2FieldAE.realization_ae haarAddCircle K hK p
      ((MeasurableL2FieldAE.section_memLp_iff haarAddCircle K hK p).mp hpK)
  have hABC:A=B-C:=by
    apply Lp.ext
    filter_upwards [ha,hb,hc,Lp.coeFn_sub B C,he] with x ha hb hc hs he
    rw [ha,hs]
    change F (p,x)=B x-C x
    rw [hb,hc]
    exact he
  change OneInputOperator.besselHalf Λ ρ hΛ hρ A=
    OneInputOperator.besselHalf Λ ρ hΛ hρ B-OneInputOperator.besselHalf Λ ρ hΛ hρ C
  rw [hABC,map_sub]
end SHE.NativeBesselDifferenceIdentity
