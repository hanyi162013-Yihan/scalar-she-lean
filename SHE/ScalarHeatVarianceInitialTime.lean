module

public import SHE.PolynomialInitialAgeTime
public import SHE.ScalarHeatVarianceEnergy
public import SHE.PolynomialEnergyDomination
public import SHE.ScalarHeatBandTime

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2500000
namespace SHE.ScalarHeatVarianceInitialTime
open Set MeasureTheory ProbabilityTheory Real ScalarHeatBandEnvelope ScalarGaussianSemigroup SmoothCylinders
open scoped NNReal
variable {X : Type*} [MeasurableSpace X] (ν : Measure X) [IsProbabilityMeasure ν]

/-- Both endpoint faces of the actual changed-variance slot are retained.
The original singular initial-profile power costs exactly h^p; the
future covariance gain pays for two state derivatives, preserving the
full beta+2rho frequency exponent without an exponential-band premise. -/
theorem energy {a : ℝ→ℝ} (ha : BoundedSmooth a) {H β ρ c h E p : ℝ}
    (hH : 0≤H) (hβ : 0≤β) (hβ1 : β≤1) (hρ0 : -(1/2:ℝ)<ρ) (hρ1 : ρ<1/2) (hc : 0<c) (hE : 0≤E)
    (hh0 : 0<h) (hp0 : -1<p) (hp1 : p≤0)
    (hh : ∀ x y,|a x-a y|≤H*|x-y|^β) (σ0 σ1 m : ℝ×X→ℝ)
    (h0m : Measurable σ0) (h1m : Measurable σ1) (hmm : Measurable m)
    (h0 : ∀ t∈Ioo (0:ℝ) h,∀ᵐ z∂ν,c*sqrt t≤σ0 (t,z))
    (h1 : ∀ t∈Ioo (0:ℝ) h,∀ᵐ z∂ν,c*sqrt t≤σ1 (t,z))
    (hdi : ∀ t∈Ioo (0:ℝ) h,Integrable (fun z=>(σ1 (t,z)-σ0 (t,z))^2) ν)
    (hbudget : ∀ t∈Ioo (0:ℝ) h,(∫ z,(σ1 (t,z)-σ0 (t,z))^2 ∂ν)≤E*t*(h-t)^p) (j : ℕ) :
    let g:=fun p=>deriv (heat (σ1 p).toNNReal (ScalarHeatBands.band a (j+1))) (m p)-
      deriv (heat (σ0 p).toNNReal (ScalarHeatBands.band a (j+1))) (m p)
    let r:=CompactMollifier.radius (j+1)
    IntegrableOn (fun t=>t^(ρ-1/2)*(∫ z,|g (t,z)|^2 ∂ν)) (Ioc (0:ℝ) h) ∧
      (∫ t in Ioc (0:ℝ) h,t^(ρ-1/2)*(∫ z,|g (t,z)|^2 ∂ν))≤
        ((1/2:ℝ)*H*constant β 2)^2*
          (((1/2:ℝ)^p)*(1/(ρ+3/2)+1/(1-β/2-ρ))+2/(p+1))*
          c^(-3-2*ρ)*r^(2*β+4*ρ)*E*h^p := by
  intro g r
  let A:=(1/2:ℝ)*H*constant β 2
  let L:=c^2/r^4
  let K:=A^2*r^(2*β-6)*E
  let G:=fun t=>t^(ρ-1/2)*(∫ z,|g (t,z)|^2 ∂ν)
  have hr : 0<r:=CompactMollifier.radius_pos (j+1)
  have hL : 0<L:=div_pos (sq_pos_of_pos hc) (pow_pos hr 4)
  have hK : 0≤K:=mul_nonneg (mul_nonneg (sq_nonneg _) (rpow_nonneg hr.le _)) hE
  have hg : Measurable g:=
    (PolynomialGaussianDecay.derivative_measurable ha (j+1) σ1 m h1m hmm).sub
      (PolynomialGaussianDecay.derivative_measurable ha (j+1) σ0 m h0m hmm)
  have hmean : Measurable (fun t : ℝ=>∫ z,|g (t,z)|^2 ∂ν):=
    ((continuous_abs.measurable.comp hg).pow_const 2).stronglyMeasurable.integral_prod_right.measurable
  have hG : Measurable G:=by
    have hw : Measurable (fun t : ℝ=>t^(ρ-1/2)):=by fun_prop
    convert! hw.mul hmean using 1
  have hb (t : ℝ) (ht : t∈Ioo (0:ℝ) h) : |G t|≤K*((h-t)^p*PolynomialGaussianTime.kernel (ρ+3/2) ((5-β)/2) L t):=by
    let lo:=c*sqrt t
    have hlo : 0<lo:=mul_pos hc (sqrt_pos.2 ht.1)
    have hm (f : ℝ×X→ℝ) (hf : Measurable f) : Measurable (fun z=>f (t,z)):=
      hf.comp (measurable_const.prodMk measurable_id)
    have he:=ScalarHeatVarianceEnergy.energy ν ha hH hβ hβ1 hlo hh j
      (fun z=>σ0 (t,z)) (fun z=>σ1 (t,z)) (fun z=>m (t,z))
      (hm σ0 h0m) (hm σ1 h1m) (hm m hmm) (h0 t ht) (h1 t ht) (hdi t ht)
    change Integrable (fun z=>|g (t,z)|^2) ν ∧
      (∫ z,|g (t,z)|^2 ∂ν)≤(A*r^(β-3)*decay r lo ((5-β)/2))^2*
        (∫ z,(σ1 (t,z)-σ0 (t,z))^2 ∂ν) at he
    have hd:=PolynomialGaussianDecay.decay_sq_bound hr hc ht.1 (show 0≤(5-β)/2 by linarith) (σ:=lo) le_rfl
    have hrpow : (r^(β-3))^2=r^(2*β-6):=by
      rw [←Real.rpow_two,←Real.rpow_mul hr.le]
      congr 1
      ring
    have hs':=he.2.trans (mul_le_mul_of_nonneg_left (hbudget t ht) (sq_nonneg _))
    simp only [mul_pow,hrpow] at hs'
    have hbound : (∫ z,|g (t,z)|^2 ∂ν)≤A^2*r^(2*β-6)*min 1 ((L*t)^(-((5-β)/2)))*(E*t*(h-t)^p):=
      hs'.trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hd (mul_nonneg (sq_nonneg A) (rpow_nonneg hr.le _))) (mul_nonneg (mul_nonneg hE ht.1.le) (rpow_nonneg (by linarith [ht.2]) _)))
    have htime : t^(ρ-1/2)*t=t^(ρ+1/2) := by
      calc
        _=t^(ρ-1/2)*t^(1:ℝ):=by rw [Real.rpow_one]
        _=_:=by rw [←Real.rpow_add ht.1];congr 1;ring
    rw [abs_of_nonneg (mul_nonneg (rpow_nonneg ht.1.le _) (integral_nonneg (fun _=>sq_nonneg _)))]
    calc
      _≤t^(ρ-1/2)*(A^2*r^(2*β-6)*min 1 ((L*t)^(-((5-β)/2)))*(E*t*(h-t)^p)):=
        mul_le_mul_of_nonneg_left hbound (rpow_nonneg ht.1.le _)
      _=K*((h-t)^p*((t^(ρ-1/2)*t)*min 1 ((L*t)^(-((5-β)/2))))):=by dsimp only [K];ring
      _=_:=by rw [htime];dsimp only [PolynomialGaussianTime.kernel];rw [show ρ+3/2-1=ρ+1/2 by ring]
  have he:=PolynomialInitialAgeTime.dominated (by linarith : 0<ρ+3/2)
    (by linarith : ρ+3/2<(5-β)/2) hL hK hh0 hp0 hp1 G hG hb
  refine ⟨he.1,he.2.trans_eq ?_⟩
  have hscale:=ScalarHeatBandTime.scale_factor (β:=β-2) (ρ:=ρ+1) hr hc
  have hscale' : r^(2*β-6)*(c^2/r^4)^(-(ρ+3/2))=c^(-3-2*ρ)*r^(2*β+4*ρ):=by
    convert hscale using 1 <;> congr 2 <;> ring
  dsimp only [K,L]
  rw [show (5-β)/2-(ρ+3/2)=1-β/2-ρ by ring]
  calc
    _=A^2*(((1/2:ℝ)^p)*(1/(ρ+3/2)+1/(1-β/2-ρ))+2/(p+1))*
        (r^(2*β-6)*(c^2/r^4)^(-(ρ+3/2)))*E*h^p:=by ring
    _=_:=by rw [hscale'];dsimp only [A];ring

end SHE.ScalarHeatVarianceInitialTime
