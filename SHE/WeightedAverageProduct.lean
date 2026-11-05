module
public import SHE.WeightedBorelAverage
public import Mathlib.MeasureTheory.Integral.Prod
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
namespace SHE.WeightedAverageProduct
open MeasureTheory GaussianIncrement WeightedBorelAverage
variable {X Y:Type*} [MeasurableSpace X] [MeasurableSpace Y] {n:ℕ}
variable (μ:Measure X) (ν:Measure Y) [SFinite μ] [SFinite ν]
variable (w:X→ℝ) (v:Y→ℝ) (hw:Integrable w μ) (hv:Integrable v ν)
variable (shift:X→State n) (other:Y→State n) (hs:Measurable shift) (ht:Measurable other)
variable (F:State n→ℝ) (hF:Measurable F) (M:ℝ) (hb:∀z,|F z|≤M)

include hw hv hs ht hF hb

theorem integrable (z:State n):Integrable
    (fun p:X×Y=>(w p.1*v p.2)*F (z+(shift p.1+other p.2))) (μ.prod ν):=by
  apply (hw.mul_prod hv).mul_bdd
    (hF.comp (measurable_const.add ((hs.comp measurable_fst).add (ht.comp measurable_snd)))).aestronglyMeasurable
  exact ae_of_all _ (fun p=>by simpa only [Real.norm_eq_abs,Function.comp_apply,Pi.add_apply] using hb (z+(shift p.1+other p.2)))

/-- Exact product representation of two integrable old weights. The
bounded Borel test retains all correlations and both actual shifts. -/
theorem product (z:State n):
    average μ w shift (average ν v other F) z=
      average (μ.prod ν) (fun p:X×Y=>w p.1*v p.2) (fun p=>shift p.1+other p.2) F z:=by
  have hi:=integrable μ ν w v hw hv shift other hs ht F hF M hb z
  simp only [WeightedBorelAverage.average]
  rw [integral_prod _ hi]
  apply integral_congr_ae
  filter_upwards with x
  rw [←integral_const_mul]
  apply integral_congr_ae
  filter_upwards with y
  simp only [mul_assoc,add_assoc]

/-- Fubini for arbitrary fixed integrable score weights and a bounded
Borel whole test. No independence of the test coordinates is assumed. -/
theorem commute (z:State n):
    average μ w shift (average ν v other F) z=
      average ν v other (average μ w shift F) z:=by
  rw [product μ ν w v hw hv shift other hs ht F hF M hb]
  have hi:=integrable μ ν w v hw hv shift other hs ht F hF M hb z
  simp only [WeightedBorelAverage.average]
  rw [integral_prod _ hi,integral_integral_swap hi]
  apply integral_congr_ae
  filter_upwards with y
  rw [←integral_const_mul]
  apply integral_congr_ae
  filter_upwards with x
  have he:z+(shift x+other y)=z+other y+shift x:=by abel
  rw [he]
  ring
end SHE.WeightedAverageProduct
