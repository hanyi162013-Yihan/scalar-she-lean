module
public import SHE.GammaPositiveIntegralSplit
@[expose] public section
noncomputable section
set_option autoImplicit false
namespace SHE.GammaPositiveIteratedSplit
open MeasureTheory
open scoped ENNReal
variable {X Y:Type*} [MeasurableSpace X] [MeasurableSpace Y]
/-- Split the exact six-slot density in its original iterated parameter
and sample integrals. Only ordinary joint Borel measurability is used;
there is no joint-in-past choice of reference modifications. -/
theorem split (ν:Measure X) (μ:Measure Y) [SFinite μ]
    (s f d0 d1 d2 d3:X×Y→ℝ)
    (hs:Measurable s) (hf:Measurable f) (h0:Measurable d0) (h1:Measurable d1)
    (h2:Measurable d2) (h3:Measurable d3) {K:ℝ} (hK:0≤K):
    (∫⁻x,∫⁻y,ENNReal.ofReal (6*(s (x,y)+f (x,y)+K*(d0 (x,y)+d1 (x,y)+d2 (x,y)+d3 (x,y)))) ∂μ ∂ν)≤
      6*((∫⁻x,∫⁻y,ENNReal.ofReal (s (x,y)) ∂μ ∂ν)+(∫⁻x,∫⁻y,ENNReal.ofReal (f (x,y)) ∂μ ∂ν)+
        ENNReal.ofReal K*((∫⁻x,∫⁻y,ENNReal.ofReal (d0 (x,y)) ∂μ ∂ν)+(∫⁻x,∫⁻y,ENNReal.ofReal (d1 (x,y)) ∂μ ∂ν)+
          (∫⁻x,∫⁻y,ENNReal.ofReal (d2 (x,y)) ∂μ ∂ν)+(∫⁻x,∫⁻y,ENNReal.ofReal (d3 (x,y)) ∂μ ∂ν))):=by
  have hm:Measurable (fun p:X×Y=>ENNReal.ofReal (6*(s p+f p+K*(d0 p+d1 p+d2 p+d3 p)))):=
    (measurable_const.mul ((hs.add hf).add (measurable_const.mul (((h0.add h1).add h2).add h3)))).ennreal_ofReal
  rw [←lintegral_prod _ hm.aemeasurable]
  have he:=GammaPositiveIntegralSplit.split (ν.prod μ) s f d0 d1 d2 d3 hs hf h0 h1 h2 h3 hK
  simpa only [lintegral_prod _ hs.ennreal_ofReal.aemeasurable,
    lintegral_prod _ hf.ennreal_ofReal.aemeasurable,
    lintegral_prod _ h0.ennreal_ofReal.aemeasurable,
    lintegral_prod _ h1.ennreal_ofReal.aemeasurable,
    lintegral_prod _ h2.ennreal_ofReal.aemeasurable,
    lintegral_prod _ h3.ennreal_ofReal.aemeasurable] using he
end SHE.GammaPositiveIteratedSplit
