module
public import SHE.NativeBesselFiniteIdentity
public import SHE.NegativeThreeLeg
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
namespace SHE.NativeBesselSectionEnergy
open MeasureTheory Set StoppedFourier AddCircle
open scoped ENNReal
local instance : Fact (0<2*Real.pi):=⟨by positivity⟩
local instance : MeasurableSpace CircleL2:=borel _
local instance : BorelSpace CircleL2:=⟨rfl⟩
local instance : SecondCountableTopology CircleL2:=
  (_root_.fourierBasis (T:=2*Real.pi)).repr.toHomeomorph.secondCountableTopology
variable {P:Type*}[MeasurableSpace P]
variable (Λ ρ:ℝ)(hΛ:1≤Λ)(hρ:0≤ρ)

/-- Spatial AE equality of actual L2 sections identifies their native
versions, independently of values at other parameter points. -/
theorem congr (F G:P×HeatCircle→ℂ)(hF:Measurable F)(hG:Measurable G)(p:P)
    (hpF:MemLp (fun x=>F (p,x)) 2 haarAddCircle)
    (hpG:MemLp (fun x=>G (p,x)) 2 haarAddCircle)
    (he:∀ᵐx∂haarAddCircle,F (p,x)=G (p,x)):
    NativeBesselFieldAE.value Λ ρ hΛ hρ F p=NativeBesselFieldAE.value Λ ρ hΛ hρ G p:=by
  have hs:∀ᵐx∂haarAddCircle,F (p,x)=∑i∈({()}:Finset Unit),G (p,x):=by
    simpa only [Finset.sum_singleton] using he
  simpa only [Finset.sum_singleton] using
    NativeBesselFiniteIdentity.finite_sum Λ ρ hΛ hρ ({()}:Finset Unit)
      F hF (fun _=>G) (fun _=>hG) p hpF (fun _ _=>hpG) hs

/-- The true massive multiplier gives its sharp scalar L2 contraction.
This damping gain is used for terminal/reference terms, not inserted
into the different native kernel trace estimate. -/
theorem norm_sq_le(F:P×HeatCircle→ℂ)(hF:Measurable F)(p:P)
    (hp:MemLp (fun x=>F (p,x)) 2 haarAddCircle):
    ‖NativeBesselFieldAE.value Λ ρ hΛ hρ F p‖^2≤Λ^(-ρ)*(∫x,‖F (p,x)‖^2 ∂haarAddCircle):=by
  let A:=MeasurableL2FieldAE.realization haarAddCircle F p
  have he:A=ᵐ[haarAddCircle] (fun x=>F (p,x)):=
    MeasurableL2FieldAE.realization_ae haarAddCircle F hF p
      ((MeasurableL2FieldAE.section_memLp_iff haarAddCircle F hF p).mp hp)
  have hn:‖A‖^2=∫x,‖F (p,x)‖^2 ∂haarAddCircle:=by
    rw [StoppedFourier.L2_norm_sq_eq_integral]
    exact integral_congr_ae (he.mono (fun x hx=>congrArg (fun z:ℂ=>‖z‖^2) hx))
  exact (NativeFourierAverage.besselHalf_norm_sq_mass Λ ρ hΛ hρ A).trans_eq (by rw [hn])

/-- Finite original parameter/spatial square energy yields finite native
Hilbert energy with the exact massive damping coefficient. -/
theorem energy(η:Measure P)[SFinite η](F:P×HeatCircle→ℂ)(hF:Measurable F)
    (hE:(∫⁻p,MeasurableL2FieldAE.squareMass haarAddCircle F p ∂η)<∞):
    Integrable (fun p=>‖NativeBesselFieldAE.value Λ ρ hΛ hρ F p‖^2) η ∧
      (∫⁻p,ENNReal.ofReal (‖NativeBesselFieldAE.value Λ ρ hΛ hρ F p‖^2) ∂η)≤
        ENNReal.ofReal (Λ^(-ρ))*(∫⁻p,MeasurableL2FieldAE.squareMass haarAddCircle F p ∂η):=by
  have hg:=MeasurableL2FieldAE.good_ae haarAddCircle η F hF hE
  have hcap:(∫⁻p,ENNReal.ofReal (‖NativeBesselFieldAE.value Λ ρ hΛ hρ F p‖^2) ∂η)≤
      ENNReal.ofReal (Λ^(-ρ))*(∫⁻p,MeasurableL2FieldAE.squareMass haarAddCircle F p ∂η):=by
    rw [←lintegral_const_mul _ (MeasurableL2FieldAE.mass_measurable haarAddCircle F hF)]
    apply lintegral_mono_ae
    filter_upwards [hg] with p hp
    have hm:MemLp (fun x=>F (p,x)) 2 haarAddCircle:=
      (MeasurableL2FieldAE.section_memLp_iff haarAddCircle F hF p).mpr hp
    have hi:Integrable (fun x=>‖F (p,x)‖^2) haarAddCircle:=
      (memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).mp hm
    have he:ENNReal.ofReal (∫x,‖F (p,x)‖^2 ∂haarAddCircle)=
        MeasurableL2FieldAE.squareMass haarAddCircle F p:=
      ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ (fun x=>sq_nonneg _))
    rw [←he,←ENNReal.ofReal_mul (Real.rpow_nonneg (zero_le_one.trans hΛ) _)]
    exact ENNReal.ofReal_le_ofReal (norm_sq_le Λ ρ hΛ hρ F hF p hm)
  have hfinite:(∫⁻p,ENNReal.ofReal (‖NativeBesselFieldAE.value Λ ρ hΛ hρ F p‖^2) ∂η)<∞:=
    hcap.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hE)
  have hm:Measurable (fun p=>‖NativeBesselFieldAE.value Λ ρ hΛ hρ F p‖^2):=
    (NativeBesselFieldAE.measurable Λ ρ hΛ hρ F hF).norm.pow_const 2
  exact ⟨⟨hm.aestronglyMeasurable,
    (hasFiniteIntegral_iff_ofReal (ae_of_all _ (fun p=>sq_nonneg _))).mpr hfinite⟩,hcap⟩

/-- An actual scalar product-energy cap transfers to the same native
Hilbert sections with the exact massive factor. -/
theorem energy_of_integral_bound(η:Measure P)[SFinite η](F:P×HeatCircle→ℂ)(hF:Measurable F)
    (hi:Integrable (fun z=>‖F z‖^2) (η.prod haarAddCircle))
    (R:ℝ)(hR:(∫z,‖F z‖^2 ∂η.prod haarAddCircle)≤R):
    Integrable (fun p=>‖NativeBesselFieldAE.value Λ ρ hΛ hρ F p‖^2) η ∧
      (∫p,‖NativeBesselFieldAE.value Λ ρ hΛ hρ F p‖^2 ∂η)≤Λ^(-ρ)*R:=by
  have he:(∫⁻p,MeasurableL2FieldAE.squareMass haarAddCircle F p ∂η)=
      ENNReal.ofReal (∫z,‖F z‖^2 ∂η.prod haarAddCircle):=by
    calc
      _=(∫⁻z,ENNReal.ofReal (‖F z‖^2) ∂η.prod haarAddCircle):=
        (lintegral_prod _ ((hF.norm.pow_const 2).ennreal_ofReal).aemeasurable).symm
      _=_:=(ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ (fun z=>sq_nonneg _))).symm
  have hE:(∫⁻p,MeasurableL2FieldAE.squareMass haarAddCircle F p ∂η)<∞:=by
    rw [he]
    exact ENNReal.ofReal_lt_top
  obtain ⟨hn,hcap⟩:=energy Λ ρ hΛ hρ η F hF hE
  have hpow:0≤Λ^(-ρ):=Real.rpow_nonneg (zero_le_one.trans hΛ) _
  rw [he,←ENNReal.ofReal_mul hpow,
    ←ofReal_integral_eq_lintegral_ofReal hn (ae_of_all _ (fun p=>sq_nonneg _))] at hcap
  have hreal: (∫p,‖NativeBesselFieldAE.value Λ ρ hΛ hρ F p‖^2 ∂η)≤
      Λ^(-ρ)*(∫z,‖F z‖^2 ∂η.prod haarAddCircle):=
    (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hpow (integral_nonneg (fun z=>sq_nonneg _)))).mp hcap
  exact ⟨hn,hreal.trans (mul_le_mul_of_nonneg_left hR hpow)⟩

end SHE.NativeBesselSectionEnergy
