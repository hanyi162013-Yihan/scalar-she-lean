module

public import SHE.PolynomialGaussianDecay

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2500000
namespace SHE.ScalarHeatBandTime
open Set MeasureTheory ProbabilityTheory Real ScalarHeatBandEnvelope ScalarGaussianSemigroup SmoothCylinders
open scoped NNReal ENNReal

def massConstant (β ρ : ℝ) : ℝ:=1/(ρ+1/2)+1/(1-β/2-ρ)

theorem scale_factor {r c β ρ : ℝ} (hr : 0<r) (hc : 0<c) :
    r^(2*β-2)*(c^2/r^4)^(-(ρ+1/2))=c^(-1-2*ρ)*r^(2*β+4*ρ) := by
  rw [Real.div_rpow (sq_nonneg c) (pow_nonneg hr.le 4),←Real.rpow_natCast_mul hc.le,
    ←Real.rpow_natCast_mul hr.le,div_eq_mul_inv,←Real.rpow_neg hr.le]
  calc
    _=c^((2:ℝ)*(-(ρ+1/2)))*(r^(2*β-2)*r^(-((4:ℝ)*(-(ρ+1/2))))):=by ring
    _=_:=by
      rw [←Real.rpow_add hr]
      congr 2 <;> ring

/-- The actual first derivative of a Gaussian-heat band has a finite
physical-time square integral with the SHARP state-frequency exponent.
The current mean and future variance may be arbitrary measurable,
mutually dependent functions; only the actual elliptic lower variance
bound is used. Constants contain no unsmoothed coefficient derivatives. -/
theorem derivative_energy {a : ℝ→ℝ} (ha : BoundedSmooth a) {H β ρ c h : ℝ}
    (hH : 0≤H) (hβ : 0≤β) (hβ1 : β≤1) (hρ0 : -(1/2:ℝ)<ρ) (hρ1 : ρ<1/2) (hc : 0<c)
    (hh : ∀ x y,|a x-a y|≤H*|x-y|^β) (σ m : ℝ→ℝ) (hσm : Measurable σ) (hmm : Measurable m)
    (hσ : ∀ t∈Ioc (0:ℝ) h,c*sqrt t≤σ t) (j : ℕ) :
    IntegrableOn (fun t=>t^(ρ-1/2)*|deriv (heat (σ t).toNNReal (ScalarHeatBands.band a (j+1))) (m t)|^2)
      (Ioc 0 h) ∧
    (∫ t in Ioc (0:ℝ) h,t^(ρ-1/2)*|deriv (heat (σ t).toNNReal (ScalarHeatBands.band a (j+1))) (m t)|^2)≤
      (H*ScalarHeatBandEnvelope.constant β 0)^2*massConstant β ρ*c^(-1-2*ρ)*
        CompactMollifier.radius (j+1)^(2*β+4*ρ) := by
  let r:=CompactMollifier.radius (j+1)
  let A:=H*ScalarHeatBandEnvelope.constant β 0
  let L:=c^2/r^4
  let g:=fun t=>t^(ρ-1/2)*|deriv (heat (σ t).toNNReal (ScalarHeatBands.band a (j+1))) (m t)|^2
  let f:=fun t=>A^2*r^(2*β-2)*PolynomialGaussianTime.kernel (ρ+1/2) ((3-β)/2) L t
  have hr : 0<r:=CompactMollifier.radius_pos (j+1)
  have hA : 0≤A:=mul_nonneg hH (ScalarHeatBandEnvelope.constant_nonneg β 0)
  have hL : 0<L:=div_pos (sq_pos_of_pos hc) (pow_pos hr 4)
  have hγ : 0<ρ+1/2:=by linarith
  have hs : ρ+1/2<(3-β)/2:=by linarith
  have hf : IntegrableOn f (Ioi 0):=
    (PolynomialGaussianTime.integrable hγ hs hL).const_mul (A^2*r^(2*β-2))
  have hfm : IntegrableOn f (Ioc (0:ℝ) h):=hf.mono_set (fun _ ht=>ht.1)
  have hgmeas : Measurable g:=by
    have hd:=PolynomialGaussianDecay.derivative_measurable ha (j+1) σ m hσm hmm
    have hw : Measurable (fun t : ℝ=>t^(ρ-1/2)):=by fun_prop
    convert! hw.mul (hd.norm.pow_const 2) using 1
  have hp (t : ℝ) (ht : t∈Ioc (0:ℝ) h) : g t≤f t := by
    have hst : 0<σ t:=(mul_pos hc (sqrt_pos.2 ht.1)).trans_le (hσ t ht)
    have he:=ScalarHeatBandEnvelope.jet_bound ha hH hβ hβ1 hh (σ t).toNNReal
      (Real.toNNReal_pos.mpr hst) j 0 (m t)
    simp only [Nat.zero_add,iteratedDeriv_one,Nat.cast_zero,sub_zero,zero_add,
      Real.coe_toNNReal _ hst.le] at he
    change _≤A*r^(β-1)*decay r (σ t) ((3-β)/2) at he
    have hsq:=pow_le_pow_left₀ (abs_nonneg _) he 2
    have hd:=PolynomialGaussianDecay.decay_sq_bound hr hc ht.1
      (show 0≤(3-β)/2 by linarith) (hσ t ht)
    have hrpow : (r^(β-1))^2=r^(2*β-2):=by
      rw [←Real.rpow_two,←Real.rpow_mul hr.le]
      congr 1
      ring
    have hbound : |deriv (heat (σ t).toNNReal (ScalarHeatBands.band a (j+1))) (m t)|^2≤
        A^2*r^(2*β-2)*min 1 ((L*t)^(-((3-β)/2))) := by
      simp only [mul_pow,hrpow] at hsq
      exact hsq.trans (mul_le_mul_of_nonneg_left hd (mul_nonneg (sq_nonneg A) (rpow_nonneg hr.le _)))
    have hw : 0≤t^(ρ-1/2):=rpow_nonneg ht.1.le _
    have hm:=mul_le_mul_of_nonneg_left hbound hw
    simpa only [g,f,PolynomialGaussianTime.kernel,show ρ+1/2-1=ρ-1/2 by ring,mul_assoc,mul_left_comm,mul_comm] using hm
  have hg : IntegrableOn g (Ioc (0:ℝ) h):=by
    apply hfm.mono' hgmeas.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    change ‖g t‖≤f t
    rw [Real.norm_of_nonneg (show 0≤g t from mul_nonneg (rpow_nonneg ht.1.le _) (sq_nonneg _))]
    exact hp t ht
  refine ⟨hg,?_⟩
  have hle : (∫ t in Ioc (0:ℝ) h,g t)≤∫ t in Ioi (0:ℝ),f t := by
    apply (integral_mono_ae hg hfm (by filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht; exact hp t ht)).trans
    apply setIntegral_mono_set hf
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact mul_nonneg (mul_nonneg (sq_nonneg A) (rpow_nonneg hr.le _))
        (mul_nonneg (rpow_nonneg ht.le _) (le_min (by norm_num) (rpow_nonneg (mul_nonneg hL.le ht.le) _)))
    · exact ae_of_all _ (fun t ht=>ht.1)
  apply hle.trans_eq
  rw [show f=(fun t=>A^2*r^(2*β-2)*PolynomialGaussianTime.kernel (ρ+1/2) ((3-β)/2) L t) by rfl,
    integral_const_mul,PolynomialGaussianTime.integral hγ hs hL]
  have he := scale_factor (β:=β) (ρ:=ρ) hr hc
  dsimp only [L] at *
  rw [show (3-β)/2-(ρ+1/2)=1-β/2-ρ by ring]
  dsimp only [massConstant]
  calc
    _=A^2*(1/(ρ+1/2)+1/(1-β/2-ρ))*(r^(2*β-2)*(c^2/r^4)^(-(ρ+1/2))):=by ring
    _=_:=by rw [he]; dsimp only [A,r]; ring

end SHE.ScalarHeatBandTime
