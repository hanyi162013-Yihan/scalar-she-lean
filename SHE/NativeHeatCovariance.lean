module
public import SHE.NativeHeatQuadratic
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
namespace SHE.NativeHeatCovariance
open Set MeasureTheory Real AddCircle StoppedFourier NativeHeatQuadratic
open scoped NNReal ENNReal
local instance : Fact (0<2*Real.pi):=⟨by positivity⟩
variable {Ω:Type*}[MeasurableSpace Ω](μ:Measure Ω)[IsProbabilityMeasure μ]

/-- The actual native heated L2 energy averaged over the original
sample measure is the positive heat kernel paired with the true
uncentered two-point covariance. -/
theorem energy {t:ℝ}(ht:0<t)(f:Ω→CircleL2)(F:Ω×HeatCircle→ℝ)
    (hF:Measurable F){B:ℝ}(hB:0≤B)(hb:∀p,|F p|≤B)
    (hf:∀ᵐω∂μ,(f ω:HeatCircle→ℂ)=ᵐ[haarAddCircle] fun x=>(F (ω,x):ℂ)):
    (∫ω,‖circleHeatOperator (t/2) (by positivity) (f ω)‖^2 ∂μ)=
      ∫z:HeatCircle×HeatCircle,K t ht z*(∫ω,F (ω,z.1)*F (ω,z.2) ∂μ)
        ∂haarAddCircle.prod haarAddCircle:=by
  let Q:Ω×(HeatCircle×HeatCircle)→ℝ:=fun p=>K t ht p.2*F (p.1,p.2.1)*F (p.1,p.2.2)
  let C:ℝ:=1+heatConstant*(t/2)^(-(1/2:ℝ))
  have hC:0≤C:=by dsimp [C];exact add_nonneg (by norm_num) (mul_nonneg heatConstant_pos.le (Real.rpow_nonneg (by positivity) _))
  have hm:Measurable Q:=by
    exact (((measurable_K ht).comp measurable_snd).mul
      (hF.comp (measurable_fst.prodMk (measurable_fst.comp measurable_snd)))).mul
      (hF.comp (measurable_fst.prodMk (measurable_snd.comp measurable_snd)))
  have hi:Integrable Q (μ.prod (haarAddCircle.prod haarAddCircle)):=by
    apply (integrable_const (C*B^2)).mono' hm.aestronglyMeasurable
    filter_upwards with p
    change ‖K t ht p.2*F (p.1,p.2.1)*F (p.1,p.2.2)‖≤C*B^2
    rw [Real.norm_eq_abs,abs_mul,abs_mul,abs_of_nonneg (show 0≤K t ht p.2 from norm_nonneg _)]
    have hh:=mul_le_mul (hb (p.1,p.2.1)) (hb (p.1,p.2.2)) (abs_nonneg _) hB
    calc
      _=K t ht p.2*(|F (p.1,p.2.1)| * |F (p.1,p.2.2)|):=by ring
      _≤C*(B*B):=mul_le_mul (K_bound ht p.2) hh (mul_nonneg (abs_nonneg _) (abs_nonneg _)) hC
      _=_:=by ring
  calc
    _=∫ω,∫z:HeatCircle×HeatCircle,Q (ω,z) ∂haarAddCircle.prod haarAddCircle ∂μ:=by
      apply integral_congr_ae
      filter_upwards [hf,hi.prod_right_ae] with ω hω hq
      rw [NativeHeatQuadratic.energy ht (f ω) (fun x=>F (ω,x)) hω,integral_prod _ hq]
    _=∫z:HeatCircle×HeatCircle,∫ω,Q (ω,z) ∂μ ∂haarAddCircle.prod haarAddCircle:=
      integral_integral_swap hi
    _=_:=by
      apply integral_congr_ae
      filter_upwards with z
      dsimp [Q]
      simp_rw [mul_assoc]
      rw [integral_const_mul]

end SHE.NativeHeatCovariance
