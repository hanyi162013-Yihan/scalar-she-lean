module

public import SHE.ScalarNegativeOutputEnergy
public import SHE.NativeBesselSectionEnergy
public import SHE.CircleNormalization

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

namespace SHE.NativeUnitRootEnergy
open Set MeasureTheory Real AddCircle StoppedFourier
open scoped ENNReal
local instance nativeUnitRootEnergy_period:Fact (0<2*π):=⟨by positivity⟩
local instance nativeUnitRootEnergy_unit:Fact (0<(1:ℝ)):=⟨zero_lt_one⟩

/-- True simultaneous unit-root energy transfers to the actual native
scalar root, with normalized Haar mass and the original massive
Bessel multiplier. -/
theorem scalar (Λ ρ:ℝ)(hΛ:1≤Λ)(hρ:0≤ρ)(F:HeatCircle→ℝ)(hF:Measurable F)
    (hi:Integrable (fun x:AddCircle (1:ℝ)=>|F (CircleNormalization.scale 1 (2*π) x)|^2) haarAddCircle):
    MemLp (fun x:HeatCircle=>(F x:ℂ)) 2 haarAddCircle ∧
      NativeFourierAverage.scalarEnergy Λ ρ (fun x:HeatCircle=>(F x:ℂ))≤
        Λ^(-ρ)*(∫x:AddCircle (1:ℝ),|F (CircleNormalization.scale 1 (2*π) x)|^2 ∂haarAddCircle):=by
  have hm:Measurable (fun x:HeatCircle=>(F x:ℂ)):=Complex.continuous_ofReal.measurable.comp hF
  have hs:=CircleNormalization.scale_measurePreserving 1 (2*π)
  have hunit:Integrable (fun x:AddCircle (1:ℝ)=>‖(F (CircleNormalization.scale 1 (2*π) x):ℂ)‖^2)
      haarAddCircle:=by simpa only [Complex.norm_real,Real.norm_eq_abs] using hi
  have hn:Integrable (fun x:HeatCircle=>‖(F x:ℂ)‖^2) haarAddCircle:=
    (hs.integrable_comp (hm.norm.pow_const 2).aestronglyMeasurable).mp hunit
  have hp:MemLp (fun x:HeatCircle=>(F x:ℂ)) 2 haarAddCircle:=
    (memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).mpr hn
  refine ⟨hp,?_⟩
  have he:=hs.integral_comp (CircleNormalization.scaleMeasurableEquiv 1 (2*π)).measurableEmbedding
    (fun x:HeatCircle=>‖(F x:ℂ)‖^2)
  have hb:=(NativeFourierAverage.scalar_negative_energy Λ ρ hΛ hρ _ hp).2
  rw [←he] at hb
  simpa only [Complex.norm_real,Real.norm_eq_abs] using hb

theorem hilbert (Λ ρ:ℝ)(hΛ:1≤Λ)(hρ:0≤ρ)(F:HeatCircle→ℝ)(hF:Measurable F)
    (hi:Integrable (fun x:AddCircle (1:ℝ)=>|F (CircleNormalization.scale 1 (2*π) x)|^2) haarAddCircle):
    ‖NativeBesselFieldAE.value Λ ρ hΛ hρ (fun z:Unit×HeatCircle=>(F z.2:ℂ)) ()‖^2≤
      Λ^(-ρ)*(∫x:AddCircle (1:ℝ),|F (CircleNormalization.scale 1 (2*π) x)|^2 ∂haarAddCircle):=by
  have hp:=(scalar Λ ρ hΛ hρ F hF hi).1
  have hm:Measurable (fun z:Unit×HeatCircle=>(F z.2:ℂ)):=
    (Complex.continuous_ofReal.measurable.comp hF).comp measurable_snd
  have hb:=NativeBesselSectionEnergy.norm_sq_le Λ ρ hΛ hρ _ hm () hp
  have he:=(CircleNormalization.scale_measurePreserving 1 (2*π)).integral_comp
    (CircleNormalization.scaleMeasurableEquiv 1 (2*π)).measurableEmbedding
    (fun x:HeatCircle=>‖(F x:ℂ)‖^2)
  rw [←he] at hb
  simpa only [Complex.norm_real,Real.norm_eq_abs] using hb

end SHE.NativeUnitRootEnergy
