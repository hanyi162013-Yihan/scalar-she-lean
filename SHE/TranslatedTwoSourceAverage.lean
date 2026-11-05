module

public import SHE.CorrelatedTwoSourceAverage
public import SHE.FractionalParentEnergy

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section
namespace SHE.TranslatedTwoSourceAverage
open Set MeasureTheory ProbabilityTheory Real AddCircle StoppedFourier
local instance translatedTwoSourceAverage_period : Fact (0<2*π):=⟨by positivity⟩
variable {Ω W:Type*} [MeasurableSpace Ω] [MeasurableSpace W]

/-- Two true physical inputs may be evaluated at different original
parent sites. Haar translation preserves each complete sample/spatial
energy before the dependent word is estimated. -/
theorem energy (μ:Measure Ω) [IsProbabilityMeasure μ] (ν:Measure W) [IsProbabilityMeasure ν]
    (F S:(Ω×HeatCircle)×W→ℝ) (hF:Measurable F) (hS:Measurable S)
    (f0 f1:Ω×HeatCircle→ℝ) (hf0:Measurable f0) (hf1:Measurable f1)
    (hi0:Integrable (fun y=>f0 y^2) (μ.prod haarAddCircle))
    (hi1:Integrable (fun y=>f1 y^2) (μ.prod haarAddCircle))
    (z0 z1:W→HeatCircle) (hz0:Measurable z0) (hz1:Measurable z1)
    (H:W→ℝ) (hH:Measurable H) (hHi:Integrable H ν) (hH0:∀w,0≤H w)
    {χ δ a C E0 E1:ℝ} (hχ:0≤χ) (hχ1:χ<1) (hδ:0≤δ) (hδ1:δ<1)
    (ha:0≤a) (hC:0≤C) (hE0:0≤E0) (hE1:0≤E1)
    (hb0:(∫y,f0 y^2 ∂μ.prod haarAddCircle)≤E0)
    (hb1:(∫y,f1 y^2 ∂μ.prod haarAddCircle)≤E1)
    (p:ℕ) (hp:0<p) (ho0:1≤(p:ℝ)*(1-χ)) (ho1:1≤(p:ℝ)*(1-δ))
    (hMom:∀ᵐ w ∂ν,Integrable (fun y=>|F (y,w)|^(2*p)) (μ.prod haarAddCircle) ∧
      (∫y,|F (y,w)|^(2*p) ∂μ.prod haarAddCircle)≤C*(H w)^(2*p))
    (hbound:∀y w,|S (y,w)|≤a*|f0 (y.1,y.2+z0 w)|^χ+|f1 (y.1,y.2+z1 w)|^δ):
    let G:=fun y=>∫w,S (y,w)*F (y,w) ∂ν
    Integrable (fun z=>S z*F z) ((μ.prod haarAddCircle).prod ν) ∧
    Integrable (fun y=>|G y|^2) (μ.prod haarAddCircle) ∧
    (∫y,|G y|^2 ∂μ.prod haarAddCircle)≤
      2*C^(1/(p:ℝ))*(a^2*E0^χ+E1^δ)*(∫w,H w ∂ν)^2:=by
  intro G
  let D0:((Ω×HeatCircle)×W)→ℝ:=fun y=>f0 (y.1.1,y.1.2+z0 y.2)
  let D1:((Ω×HeatCircle)×W)→ℝ:=fun y=>f1 (y.1.1,y.1.2+z1 y.2)
  have hd0:Measurable D0:=hf0.comp
    (measurable_fst.fst.prodMk (measurable_fst.snd.add (hz0.comp measurable_snd)))
  have hd1:Measurable D1:=hf1.comp
    (measurable_fst.fst.prodMk (measurable_fst.snd.add (hz1.comp measurable_snd)))
  have htrans (f:Ω×HeatCircle→ℝ) (hf:Measurable f)
      (hi:Integrable (fun y=>f y^2) (μ.prod haarAddCircle))
      (z:W→HeatCircle) (hz:Measurable z) (E:ℝ)
      (hb:(∫y,f y^2 ∂μ.prod haarAddCircle)≤E):
      ∀ᵐ w ∂ν,MemLp (fun y:Ω×HeatCircle=>f (y.1,y.2+z w)) 2 (μ.prod haarAddCircle) ∧
        (∫y:Ω×HeatCircle,f (y.1,y.2+z w)^2 ∂μ.prod haarAddCircle)≤E:=by
    apply ae_of_all
    intro w
    let T:(Ω×HeatCircle)≃ᵐ(Ω×HeatCircle):=
      (MeasurableEquiv.refl Ω).prodCongr (MeasurableEquiv.addRight (z w))
    have hT:MeasurePreserving T (μ.prod haarAddCircle) (μ.prod haarAddCircle):=
      (MeasurePreserving.id μ).prod (measurePreserving_add_right haarAddCircle (z w))
    have hh:=(hT.integrable_comp hi.aestronglyMeasurable).mpr hi
    have hm:Measurable (fun y:Ω×HeatCircle=>f (y.1,y.2+z w)):=
      hf.comp (measurable_fst.prodMk (measurable_snd.add measurable_const))
    refine ⟨(memLp_two_iff_integrable_sq hm.aestronglyMeasurable).mpr ?_,?_⟩
    · convert! hh using 1
    · exact (hT.integral_comp' (fun y=>f y^2)).le.trans hb
  exact CorrelatedTwoSourceAverage.energy (μ.prod haarAddCircle) ν F S D0 D1 hF hS hd0 hd1
    H hH hHi hH0 hχ hχ1 hδ hδ1 ha hC hE0 hE1 p hp ho0 ho1
    (htrans f0 hf0 hi0 z0 hz0 E0 hb0) (htrans f1 hf1 hi1 z1 hz1 E1 hb1) hMom
    (fun y=>hbound y.1 y.2)

end SHE.TranslatedTwoSourceAverage
