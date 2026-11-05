module

public import SHE.ScalarHeatGradientEnergy
public import SHE.ScalarHeatBandTime
public import SHE.PolynomialEnergyDomination

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2700000
namespace SHE.ScalarHeatGradientTime
open Set MeasureTheory ProbabilityTheory Real ScalarHeatBandEnvelope ScalarGaussianSemigroup SmoothCylinders
open scoped NNReal ENNReal
variable {X : Type*} [MeasurableSpace X] (ν : Measure X) [IsProbabilityMeasure ν]

/-- The second COMPLETE-Gamma multiplier has the sharp time-frequency
energy AND its clipped state-displacement gain. All means/variances may
be correlated on the same probability space, including sample×space.
The actual scalar field and its joint time integrability are proved. -/
theorem energy {a : ℝ→ℝ} (ha : BoundedSmooth a) {H β ρ c h E : ℝ}
    (hH : 0≤H) (hβ : 0≤β) (hβ1 : β≤1) (hρ0 : -(1/2:ℝ)<ρ) (hρ1 : ρ<1/2) (hc : 0<c) (hE : 0≤E)
    (hh : ∀ x y,|a x-a y|≤H*|x-y|^β) (σ x y : ℝ×X→ℝ)
    (hσm : Measurable σ) (hxm : Measurable x) (hym : Measurable y)
    (hσ : ∀ t∈Ioc (0:ℝ) h,∀ᵐ z∂ν,c*sqrt t≤σ (t,z))
    (hdi : ∀ t∈Ioc (0:ℝ) h,Integrable (fun z=>(y (t,z)-x (t,z))^2) ν)
    (hbudget : ∀ t∈Ioc (0:ℝ) h,(∫ z,(y (t,z)-x (t,z))^2 ∂ν)≤E) (j : ℕ) :
    let g:=fun p=>deriv (heat (σ p).toNNReal (ScalarHeatBands.band a (j+1))) (y p)-
      deriv (heat (σ p).toNNReal (ScalarHeatBands.band a (j+1))) (x p)
    let r:=CompactMollifier.radius (j+1)
    IntegrableOn (fun t=>t^(ρ-1/2)*(∫ z,|g (t,z)|^2 ∂ν)) (Ioc (0:ℝ) h) ∧
      (∫ t in Ioc (0:ℝ) h,t^(ρ-1/2)*(∫ z,|g (t,z)|^2 ∂ν))≤
        (2*H*ScalarHeatGradientDifference.constant β)^2*ScalarHeatBandTime.massConstant β ρ*c^(-1-2*ρ)*
          r^(2*β+4*ρ)*min 1 (E/r^2) := by
  let g:=fun p=>deriv (heat (σ p).toNNReal (ScalarHeatBands.band a (j+1))) (y p)-
    deriv (heat (σ p).toNNReal (ScalarHeatBands.band a (j+1))) (x p)
  let r:=CompactMollifier.radius (j+1)
  let A:=2*H*ScalarHeatGradientDifference.constant β
  let L:=c^2/r^4
  let clip:=min 1 (E/r^2)
  let K:=A^2*r^(2*β-2)*clip
  let G:=fun t=>t^(ρ-1/2)*(∫ z,|g (t,z)|^2 ∂ν)
  have hr : 0<r:=CompactMollifier.radius_pos (j+1)
  have hA : 0≤A:=mul_nonneg (mul_nonneg (by norm_num) hH) (ScalarHeatGradientDifference.constant_nonneg β)
  have hclip : 0≤clip:=le_min zero_le_one (div_nonneg hE (sq_nonneg r))
  have hL : 0<L:=div_pos (sq_pos_of_pos hc) (pow_pos hr 4)
  have hK : 0≤K:=mul_nonneg (mul_nonneg (sq_nonneg A) (rpow_nonneg hr.le _)) hclip
  have hγ : 0<ρ+1/2:=by linarith
  have hs : ρ+1/2<(3-β)/2:=by linarith
  have hg : Measurable g:=
    (PolynomialGaussianDecay.derivative_measurable ha (j+1) σ y hσm hym).sub
      (PolynomialGaussianDecay.derivative_measurable ha (j+1) σ x hσm hxm)
  have hmean : Measurable (fun t : ℝ=>∫ z,|g (t,z)|^2 ∂ν):=
    ((continuous_abs.measurable.comp hg).pow_const 2).stronglyMeasurable.integral_prod_right.measurable
  have hG : Measurable G:=by
    have hw : Measurable (fun t : ℝ=>t^(ρ-1/2)):=by fun_prop
    convert! hw.mul hmean using 1
  have hb (t : ℝ) (ht : t∈Ioc (0:ℝ) h) : |G t|≤K*PolynomialGaussianTime.kernel (ρ+1/2) ((3-β)/2) L t:=by
    let lo:=c*sqrt t
    have hlo : 0<lo:=mul_pos hc (sqrt_pos.2 ht.1)
    have hm (f : ℝ×X→ℝ) (hf : Measurable f) : Measurable (fun z=>f (t,z)):=
      hf.comp (measurable_const.prodMk measurable_id)
    have he:=ScalarHeatGradientEnergy.gradient_energy ν ha hH hβ hβ1 hlo hh
      (fun z=>σ (t,z)) (fun z=>x (t,z)) (fun z=>y (t,z))
      (hm σ hσm) (hm x hxm) (hm y hym) (hσ t ht) (hdi t ht) j
    change Integrable (fun z=>|g (t,z)|^2) ν ∧
      (∫ z,|g (t,z)|^2 ∂ν)≤(A*r^(β-1)*decay r lo ((3-β)/2))^2*
        min 1 ((∫ z,(y (t,z)-x (t,z))^2 ∂ν)/r^2) at he
    have hstate : min 1 ((∫ z,(y (t,z)-x (t,z))^2 ∂ν)/r^2)≤clip:=
      min_le_min_left 1 (div_le_div_of_nonneg_right (hbudget t ht) (sq_nonneg r))
    have hd:=PolynomialGaussianDecay.decay_sq_bound hr hc ht.1 (show 0≤(3-β)/2 by linarith) (σ:=lo) le_rfl
    have hrpow : (r^(β-1))^2=r^(2*β-2):=by
      rw [←Real.rpow_two,←Real.rpow_mul hr.le]
      congr 1
      ring
    have hbound : (∫ z,|g (t,z)|^2 ∂ν)≤A^2*r^(2*β-2)*min 1 ((L*t)^(-((3-β)/2)))*clip:=by
      have hs' := he.2.trans (mul_le_mul_of_nonneg_left hstate (sq_nonneg _))
      simp only [mul_pow,hrpow] at hs'
      exact hs'.trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hd (mul_nonneg (sq_nonneg A) (rpow_nonneg hr.le _))) hclip)
    have hnon : 0≤G t:=mul_nonneg (rpow_nonneg ht.1.le _) (integral_nonneg (fun _=>sq_nonneg _))
    rw [abs_of_nonneg hnon]
    have hm':=mul_le_mul_of_nonneg_left hbound (rpow_nonneg ht.1.le (ρ-1/2))
    simpa only [G,K,PolynomialGaussianTime.kernel,show ρ+1/2-1=ρ-1/2 by ring,mul_assoc,mul_left_comm,mul_comm] using hm'
  have hh':=PolynomialEnergyDomination.dominated hγ hs hL hK G hG hb
  refine ⟨hh'.1,hh'.2.trans_eq ?_⟩
  have he:=ScalarHeatBandTime.scale_factor (β:=β) (ρ:=ρ) hr hc
  dsimp only [K,L,ScalarHeatBandTime.massConstant]
  rw [show (3-β)/2-(ρ+1/2)=1-β/2-ρ by ring]
  calc
    _=A^2*(1/(ρ+1/2)+1/(1-β/2-ρ))*(r^(2*β-2)*(c^2/r^4)^(-(ρ+1/2)))*clip:=by ring
    _=_:=by rw [he]; dsimp only [A,r,clip]; ring

end SHE.ScalarHeatGradientTime
