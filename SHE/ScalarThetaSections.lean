module
public import SHE.ScalarFibreThetaEnergy
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace SHE.ScalarThetaSections
open Set MeasureTheory
variable {Θ X:Type*}[MeasurableSpace Θ][MeasurableSpace X]

/-- Genuine joint square integrability gives actual theta integrability
on an AE OUTPUT event, before any parameter-dependent sample bound. -/
theorem integrable_sections (τ:Measure Θ)[IsProbabilityMeasure τ]
    (ν:Measure X)[SFinite ν](G:Θ×X→ℝ)(hG:Measurable G)
    (hi:Integrable (fun z=>G z^2) (τ.prod ν)):
    ∀ᵐx∂ν,Integrable (fun θ=>G (θ,x)) τ:=by
  filter_upwards [hi.prod_left_ae] with x hx
  have hm:=hG.comp (measurable_id.prodMk (measurable_const (a:=x)))
  have hLp:MemLp (fun θ=>G (θ,x)) 2 τ:=
    (memLp_two_iff_integrable_sq hm.aestronglyMeasurable).mpr hx
  exact MemLp.integrable (by norm_num : (1:ENNReal)≤2) hLp
end SHE.ScalarThetaSections
