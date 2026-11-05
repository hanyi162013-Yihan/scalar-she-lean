module
public import SHE.NativeBesselGivenSection

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace SHE.NativeBesselReparameter
open MeasureTheory StoppedFourier AddCircle
open scoped ENNReal
local instance : Fact (0<2*Real.pi):=⟨by positivity⟩
local instance : MeasurableSpace CircleL2:=borel _
local instance : BorelSpace CircleL2:=⟨rfl⟩
local instance : SecondCountableTopology CircleL2:=
  (_root_.fourierBasis (T:=2*Real.pi)).repr.toHomeomorph.secondCountableTopology
variable {P Q:Type*}[MeasurableSpace P][MeasurableSpace Q]

/-- Native spatial realization commutes with an actual parameter
substitution once the true spatial section is in L2. -/
theorem value(Λ ρ:ℝ)(hΛ:1≤Λ)(hρ:0≤ρ)(F:P×HeatCircle→ℂ)(hF:Measurable F)
    (g:Q→P)(hg:Measurable g)(q:Q)
    (hp:MemLp (fun x=>F (g q,x)) 2 haarAddCircle):
    NativeBesselFieldAE.value Λ ρ hΛ hρ (fun z:Q×HeatCircle=>F (g z.1,z.2)) q=
      NativeBesselFieldAE.value Λ ρ hΛ hρ F (g q):=by
  have hG:Measurable (fun z:Q×HeatCircle=>F (g z.1,z.2)):=
    hF.comp ((hg.comp measurable_fst).prodMk measurable_snd)
  let A:P→CircleL2:=MeasurableL2FieldAE.realization haarAddCircle F
  have ha:A (g q)=ᵐ[haarAddCircle] (fun x=>F (g q,x)):=
    MeasurableL2FieldAE.realization_ae haarAddCircle F hF (g q)
      ((MeasurableL2FieldAE.section_memLp_iff haarAddCircle F hF (g q)).mp hp)
  exact NativeBesselGivenSection.value_eq Λ ρ hΛ hρ _ hG (fun q=>A (g q)) q ha.symm

end SHE.NativeBesselReparameter
