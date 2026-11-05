module
public import SHE.NativeBesselFieldAE
public import SHE.NativeFourierAverage
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
namespace SHE.NativeBesselParameterIntegral
open Set MeasureTheory AddCircle StoppedFourier
open scoped NNReal ENNReal
local instance : Fact (0<2*Real.pi):=⟨by positivity⟩
local instance : MeasurableSpace CircleL2:=borel _
local instance : BorelSpace CircleL2:=⟨rfl⟩
local instance : SecondCountableTopology CircleL2:=
  (_root_.fourierBasis (T:=2*Real.pi)).repr.toHomeomorph.secondCountableTopology
variable {A:Type*}[MeasurableSpace A](ν:Measure A)[SFinite ν]

def average (F:A×HeatCircle→ℂ)(z:Unit×HeatCircle):ℂ:=∫a,F (a,z.2) ∂ν

/-- Genuine scalar/Hilbert parameter averaging for the actual native
Bessel multiplier under JOINT L1. Only the scalar average itself needs
L2, which follows from the actual coarse uncut mark bound. -/
theorem integral (Λ ρ:ℝ)(hΛ:1≤Λ)(hρ:0≤ρ)(F:A×HeatCircle→ℂ)(hF:Measurable F)
    (hi:Integrable F (ν.prod haarAddCircle))
    (hsec:∀ᵐa∂ν,MemLp (fun x=>F (a,x)) 2 haarAddCircle)
    (hv:Integrable (NativeBesselFieldAE.value Λ ρ hΛ hρ F) ν)
    (havg:MemLp (fun x:HeatCircle=>∫a,F (a,x) ∂ν) 2 haarAddCircle):
    NativeBesselFieldAE.value Λ ρ hΛ hρ (average ν F) ()=
      ∫a,NativeBesselFieldAE.value Λ ρ hΛ hρ F a ∂ν:=by
  have hgm:Measurable (average ν F):=hF.stronglyMeasurable.integral_prod_left'.measurable.comp measurable_snd
  have hg:MeasurableL2FieldAE.squareMass haarAddCircle (average ν F) ()<∞:=
    (MeasurableL2FieldAE.section_memLp_iff haarAddCircle (average ν F) hgm ()).mp havg
  have hc:=NativeFourierAverage.weighted_average ν
    (NativeBesselFieldAE.value Λ ρ hΛ hρ F) F hv hi
    (fun l:ℤ=>(((Λ+(l:ℝ)^2)^(-ρ/2):ℝ):ℂ)) (by
      filter_upwards [hsec] with a ha
      exact NativeBesselFieldAE.coefficients Λ ρ hΛ hρ F hF a
        ((MeasurableL2FieldAE.section_memLp_iff haarAddCircle F hF a).mp ha))
  apply (fourierBasis (T:=2*Real.pi)).repr.injective
  apply lp.ext
  funext l
  simp only [fourierBasis_repr,NativeBesselFieldAE.coefficients Λ ρ hΛ hρ (average ν F) hgm () hg]
  exact (hc l).symm

/-- Pathwise native Minkowski for the literal scalar parameter average.
The integrable sharp norm envelope is applied before any stochastic
square; actual Fourier/Bochner commutation is derived above. -/
theorem norm_le (Λ ρ:ℝ)(hΛ:1≤Λ)(hρ:0≤ρ)(F:A×HeatCircle→ℂ)(hF:Measurable F)
    (hi:Integrable F (ν.prod haarAddCircle))
    (hsec:∀ᵐa∂ν,MemLp (fun x=>F (a,x)) 2 haarAddCircle)
    (havg:MemLp (fun x:HeatCircle=>∫a,F (a,x) ∂ν) 2 haarAddCircle)
    (M:A→ℝ)(hMi:Integrable M ν)
    (hb:∀ᵐa∂ν,‖NativeBesselFieldAE.value Λ ρ hΛ hρ F a‖≤M a):
    ‖NativeBesselFieldAE.value Λ ρ hΛ hρ (average ν F) ()‖≤∫a,M a ∂ν:=by
  have hv:Integrable (NativeBesselFieldAE.value Λ ρ hΛ hρ F) ν:=
    hMi.mono' (NativeBesselFieldAE.measurable Λ ρ hΛ hρ F hF).aestronglyMeasurable hb
  rw [integral ν Λ ρ hΛ hρ F hF hi hsec hv havg]
  exact norm_integral_le_of_norm_le hMi hb

end SHE.NativeBesselParameterIntegral
