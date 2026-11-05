module
public import SHE.NativeBesselParameterIntegral
public import SHE.NativeBesselGivenSection
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace SHE.NativeBesselParameterAverageAE
open MeasureTheory StoppedFourier AddCircle
local instance : Fact (0<2*Real.pi):=⟨by positivity⟩
local instance : MeasurableSpace CircleL2:=borel _
local instance : BorelSpace CircleL2:=⟨rfl⟩
local instance : SecondCountableTopology CircleL2:=
  (_root_.fourierBasis (T:=2*Real.pi)).repr.toHomeomorph.secondCountableTopology
variable {A P:Type*}[MeasurableSpace A][MeasurableSpace P]

/-- Parameter Minkowski identifies the actual output field through
its spatial AE equality; Fubini need not produce a pointwise version. -/
theorem norm_le (ν:Measure A)[SFinite ν]
    (Λ ρ:ℝ)(hΛ:1≤Λ)(hρ:0≤ρ)(F:A×HeatCircle→ℂ)(hF:Measurable F)
    (hi:Integrable F (ν.prod haarAddCircle))
    (hsec:∀ᵐa∂ν,MemLp (fun x=>F (a,x)) 2 haarAddCircle)
    (G:P×HeatCircle→ℂ)(hG:Measurable G)(p:P)
    (hGp:MemLp (fun x=>G (p,x)) 2 haarAddCircle)
    (he:(fun x=>G (p,x))=ᵐ[haarAddCircle] fun x=>∫a,F (a,x) ∂ν)
    (M:A→ℝ)(hMi:Integrable M ν)
    (hb:∀ᵐa∂ν,‖NativeBesselFieldAE.value Λ ρ hΛ hρ F a‖≤M a):
    ‖NativeBesselFieldAE.value Λ ρ hΛ hρ G p‖≤∫a,M a ∂ν:=by
  have havg:MemLp (fun x:HeatCircle=>∫a,F (a,x) ∂ν) 2 haarAddCircle:=
    (memLp_congr_ae he).mp hGp
  let R:=MeasurableL2FieldAE.realization haarAddCircle G p
  have hR:R=ᵐ[haarAddCircle] fun x=>G (p,x):=
    MeasurableL2FieldAE.realization_ae haarAddCircle G hG p
      ((MeasurableL2FieldAE.section_memLp_iff haarAddCircle G hG p).mp hGp)
  have hgm:Measurable (NativeBesselParameterIntegral.average ν F):=
    hF.stronglyMeasurable.integral_prod_left'.measurable.comp measurable_snd
  have ha:=NativeBesselGivenSection.value_eq Λ ρ hΛ hρ
    (NativeBesselParameterIntegral.average ν F) hgm (fun _:Unit=>R) ()
      (he.symm.trans hR.symm)
  have hg:=NativeBesselGivenSection.value_eq Λ ρ hΛ hρ G hG
    (fun _:P=>R) p hR.symm
  rw [←ha] at hg
  rw [hg]
  exact NativeBesselParameterIntegral.norm_le ν Λ ρ hΛ hρ F hF hi hsec havg M hMi hb
end SHE.NativeBesselParameterAverageAE
