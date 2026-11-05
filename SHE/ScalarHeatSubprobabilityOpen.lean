module

public import SHE.ScalarHeatGradientTime
public import SHE.PolynomialEnergyOpen

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2800000
namespace SHE.ScalarHeatSubprobabilityOpen
open Set MeasureTheory ProbabilityTheory Real ScalarHeatBandEnvelope ScalarGaussianSemigroup SmoothCylinders ScalarHeatGradientEnergy
open scoped NNReal ENNReal
variable {X : Type*} [MeasurableSpace X] (ν : Measure X) [IsFiniteMeasure ν]

/-! The complete-root estimates also apply to original finite past-time
× sample × space measures of mass at most one. Thus no artificial
probability normalization of the moving past is needed. -/

/-- A physical state displacement may be correlated with everything
else. Its clipped square averages to the minimum of one and its actual
L² energy at the band scale. -/
theorem integral_clip (hmass : ν.real univ≤1) {d : X→ℝ} (hd : Measurable d) (hi : Integrable (fun x=>d x^2) ν)
    {r : ℝ} (hr : 0<r) :
    Integrable (fun x=>(min 1 (|d x|/r))^2) ν ∧
    (∫ x,(min 1 (|d x|/r))^2 ∂ν)≤min 1 ((∫ x,d x^2 ∂ν)/r^2) := by
  have hm : Measurable (fun x=>(min 1 (|d x|/r))^2):=by
    have ha:=continuous_abs.measurable.comp hd
    exact ((measurable_const.min (ha.div_const r)).pow_const 2)
  have hnon (x : X) : 0≤min 1 (|d x|/r):=le_min zero_le_one (div_nonneg (abs_nonneg _) hr.le)
  have hpoint (x : X) : (min 1 (|d x|/r))^2≤1:=
    (pow_le_pow_left₀ (hnon x) (min_le_left _ _) 2).trans_eq (by norm_num)
  have hI : Integrable (fun x=>(min 1 (|d x|/r))^2) ν:=
    (integrable_const (1:ℝ)).mono' hm.aestronglyMeasurable (ae_of_all _ (fun x=>by
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      exact hpoint x))
  refine ⟨hI,le_min ?_ ?_⟩
  · exact (show (∫ x,(min 1 (|d x|/r))^2 ∂ν)≤ν.real univ by
      simpa only [integral_const,smul_eq_mul,mul_one] using
        integral_mono hI (integrable_const (1:ℝ)) hpoint).trans hmass
  · have hdom (x : X) : (min 1 (|d x|/r))^2≤d x^2/r^2:=by
      have hh:=pow_le_pow_left₀ (hnon x) (min_le_right 1 (|d x|/r)) 2
      simpa only [div_pow,sq_abs] using hh
    simpa only [integral_div] using integral_mono hI (hi.div_const (r^2)) hdom


/-- The literal gradient-displacement multiplier has its clipped L²
state gain BEFORE any stochastic or spatial averaging. Future variance,
current means and every coefficient may be mutually dependent. -/
theorem gradient_energy (hmass : ν.real univ≤1) {a : ℝ→ℝ} (ha : BoundedSmooth a) {H β lo : ℝ}
    (hH : 0≤H) (hβ : 0≤β) (hβ1 : β≤1) (hlo : 0<lo)
    (hh : ∀ x y,|a x-a y|≤H*|x-y|^β) (σ x y : X→ℝ)
    (hσm : Measurable σ) (hxm : Measurable x) (hym : Measurable y)
    (hσ : ∀ᵐ z∂ν,lo≤σ z) (hi : Integrable (fun z=>(y z-x z)^2) ν) (j : ℕ) :
    let g:=fun z=>deriv (heat (σ z).toNNReal (ScalarHeatBands.band a (j+1))) (y z)-
      deriv (heat (σ z).toNNReal (ScalarHeatBands.band a (j+1))) (x z)
    let r:=CompactMollifier.radius (j+1)
    let C:=(2*H*ScalarHeatGradientDifference.constant β)*r^(β-1)*decay r lo ((3-β)/2)
    Integrable (fun z=>|g z|^2) ν ∧
      (∫ z,|g z|^2 ∂ν)≤C^2*min 1 ((∫ z,(y z-x z)^2 ∂ν)/r^2) := by
  let g:=fun z=>deriv (heat (σ z).toNNReal (ScalarHeatBands.band a (j+1))) (y z)-
    deriv (heat (σ z).toNNReal (ScalarHeatBands.band a (j+1))) (x z)
  let r:=CompactMollifier.radius (j+1)
  let C:=(2*H*ScalarHeatGradientDifference.constant β)*r^(β-1)*decay r lo ((3-β)/2)
  have hr : 0<r:=CompactMollifier.radius_pos (j+1)
  have hclip:=integral_clip ν hmass (hym.sub hxm) hi hr
  have hgm : Measurable g:=
    (PolynomialGaussianDecay.derivative_measurable ha (j+1) σ y hσm hym).sub
      (PolynomialGaussianDecay.derivative_measurable ha (j+1) σ x hσm hxm)
  have hs : 0≤(3-β)/2:=by linarith
  have hcoef : 0≤(2*H*ScalarHeatGradientDifference.constant β)*r^(β-1):=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hH) (ScalarHeatGradientDifference.constant_nonneg β))
      (rpow_nonneg hr.le _)
  have hC : 0≤C:=mul_nonneg hcoef (le_min zero_le_one (rpow_nonneg (div_nonneg hlo.le (sq_nonneg r)) _))
  have hpoint : ∀ᵐ z∂ν,|g z|^2≤C^2*(min 1 (|y z-x z|/r))^2 := by
    filter_upwards [hσ] with z hz
    have hz0 : 0<σ z:=hlo.trans_le hz
    have hh':=ScalarHeatGradientDifference.gradient_difference ha hH hβ hβ1 hh (σ z).toNNReal
      (Real.toNNReal_pos.mpr hz0) j (x z) (y z)
    rw [Real.coe_toNNReal _ hz0.le] at hh'
    have hdec:=decay_variance hr hlo hs hz
    have hclip0 : 0≤min 1 (|y z-x z|/r):=le_min zero_le_one (div_nonneg (abs_nonneg _) hr.le)
    have hbound : |g z|≤C*min 1 (|y z-x z|/r):=hh'.trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hdec hcoef) hclip0)
    simpa only [mul_pow] using pow_le_pow_left₀ (abs_nonneg _) hbound 2
  have hg : Integrable (fun z=>|g z|^2) ν:=by
    apply (hclip.1.const_mul (C^2)).mono'
      ((continuous_abs.measurable.comp hgm).pow_const 2).aestronglyMeasurable
    filter_upwards [hpoint] with z hz
    simpa only [Real.norm_of_nonneg (sq_nonneg _),Function.comp_def,Pi.sub_apply] using hz
  refine ⟨hg,?_⟩
  calc
    _≤∫ z,C^2*(min 1 (|y z-x z|/r))^2 ∂ν:=integral_mono_ae hg (hclip.1.const_mul (C^2)) hpoint
    _=C^2*∫ z,(min 1 (|y z-x z|/r))^2 ∂ν:=integral_const_mul _ _
    _≤_:=mul_le_mul_of_nonneg_left hclip.2 (sq_nonneg C)


/-- The second COMPLETE-Gamma multiplier has the sharp time-frequency
energy AND its clipped state-displacement gain. All means/variances may
be correlated on the same probability space, including sample×space.
The actual scalar field and its joint time integrability are proved. -/
theorem energy (hmass : ν.real univ≤1) {a : ℝ→ℝ} (ha : BoundedSmooth a) {H β ρ c h E : ℝ}
    (hH : 0≤H) (hβ : 0≤β) (hβ1 : β≤1) (hρ0 : -(1/2:ℝ)<ρ) (hρ1 : ρ<1/2) (hc : 0<c) (hE : 0≤E)
    (hh : ∀ x y,|a x-a y|≤H*|x-y|^β) (σ x y : ℝ×X→ℝ)
    (hσm : Measurable σ) (hxm : Measurable x) (hym : Measurable y)
    (hσ : ∀ t∈Ioo (0:ℝ) h,∀ᵐ z∂ν,c*sqrt t≤σ (t,z))
    (hdi : ∀ t∈Ioo (0:ℝ) h,Integrable (fun z=>(y (t,z)-x (t,z))^2) ν)
    (hbudget : ∀ t∈Ioo (0:ℝ) h,(∫ z,(y (t,z)-x (t,z))^2 ∂ν)≤E) (j : ℕ) :
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
  have hb (t : ℝ) (ht : t∈Ioo (0:ℝ) h) : |G t|≤K*PolynomialGaussianTime.kernel (ρ+1/2) ((3-β)/2) L t:=by
    let lo:=c*sqrt t
    have hlo : 0<lo:=mul_pos hc (sqrt_pos.2 ht.1)
    have hm (f : ℝ×X→ℝ) (hf : Measurable f) : Measurable (fun z=>f (t,z)):=
      hf.comp (measurable_const.prodMk measurable_id)
    have he:=gradient_energy ν hmass ha hH hβ hβ1 hlo hh
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
  have hh':=PolynomialEnergyOpen.dominated hγ hs hL hK G hG hb
  refine ⟨hh'.1,hh'.2.trans_eq ?_⟩
  have he:=ScalarHeatBandTime.scale_factor (β:=β) (ρ:=ρ) hr hc
  dsimp only [K,L,ScalarHeatBandTime.massConstant]
  rw [show (3-β)/2-(ρ+1/2)=1-β/2-ρ by ring]
  calc
    _=A^2*(1/(ρ+1/2)+1/(1-β/2-ρ))*(r^(2*β-2)*(c^2/r^4)^(-(ρ+1/2)))*clip:=by ring
    _=_:=by rw [he]; dsimp only [A,r,clip]; ring

end SHE.ScalarHeatSubprobabilityOpen
