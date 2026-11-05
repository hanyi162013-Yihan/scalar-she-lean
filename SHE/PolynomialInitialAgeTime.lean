module

public import SHE.PolynomialEnergyDomination
public import SHE.ProfileVolterra

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency true
noncomputable section

namespace SHE.PolynomialInitialAgeTime
open Set MeasureTheory Real PolynomialGaussianTime

/-- A positive polynomial Gaussian time kernel has a scale-uniform
inverse-time cap. This is used only away from its initial face. -/
theorem kernel_cap {γ s L t:ℝ} (hγ:0<γ) (hs:γ<s) (hL:0<L) (ht:0<t):
    kernel γ s L t≤L^(-γ)/t:=by
  have hunit {x:ℝ} (hx:0<x):kernel γ s 1 x≤x^(-1:ℝ):=by
    by_cases hx1:x≤1
    · rw [unit_head (hγ.le.trans hs.le) ⟨hx,hx1⟩]
      have hp:x^γ≤1:=rpow_le_one hx.le hx1 hγ.le
      calc
        _=x^(-1:ℝ)*x^γ:=by rw [←rpow_add hx];congr 1;ring
        _≤x^(-1:ℝ)*1:=mul_le_mul_of_nonneg_left hp (rpow_nonneg hx.le _)
        _=_:=mul_one _
    · have hx1':1<x:=lt_of_not_ge hx1
      rw [unit_tail (hγ.le.trans hs.le) hx1']
      have hp:x^(γ-s)≤1:=by
        simpa only [one_rpow] using rpow_le_rpow_of_nonpos zero_lt_one hx1'.le (by linarith : γ-s≤0)
      calc
        _=x^(-1:ℝ)*x^(γ-s):=by rw [←rpow_add hx];congr 1;ring
        _≤x^(-1:ℝ)*1:=mul_le_mul_of_nonneg_left hp (rpow_nonneg hx.le _)
        _=_:=mul_one _
  rw [scale_eq hL ht.le]
  have hp:=mul_le_mul_of_nonneg_left (hunit (mul_pos hL ht)) (rpow_nonneg hL.le (1-γ))
  apply hp.trans_eq
  rw [mul_rpow hL.le ht.le]
  have he:L^(1-γ)*L^(-1:ℝ)=L^(-γ):=by
    rw [←rpow_add hL]
    congr 1
    ring
  rw [←mul_assoc,he,rpow_neg_one,div_eq_mul_inv]

/-- The integrable initial profile power may multiply the entire
future kernel, including both endpoint faces. The full frequency mass
L^(-gamma) survives and the only cost is the literal h^p factor. -/
theorem dominated {γ s L K h p:ℝ} (hγ:0<γ) (hs:γ<s) (hL:0<L)
    (hK:0≤K) (hh:0<h) (hp0:-1<p) (hp1:p≤0)
    (G:ℝ→ℝ) (hG:Measurable G)
    (hb:∀t∈Ioo 0 h,|G t|≤K*((h-t)^p*kernel γ s L t)):
    IntegrableOn G (Ioc (0:ℝ) h) ∧
      (∫t in Ioc (0:ℝ) h,G t)≤
        K*(((1/2:ℝ)^p)*(1/γ+1/(s-γ))+2/(p+1))*h^p*L^(-γ):=by
  let R:ℝ:=(1/2:ℝ)^p*h^p
  let T:ℝ:=2/h*L^(-γ)
  let D:ℝ→ℝ:=fun t=>K*(R*kernel γ s L t+T*(h-t)^p)
  have hR:0≤R:=by dsimp only [R];positivity
  have hT:0≤T:=by dsimp only [T];positivity
  have hker:IntegrableOn (kernel γ s L) (Ioc (0:ℝ) h):=
    (PolynomialGaussianTime.integrable hγ hs hL).mono_set (fun t ht=>ht.1)
  have hpow:IntegrableOn (fun t=>(h-t)^p) (Ioc (0:ℝ) h):=by
    have hi:=((intervalIntegral.intervalIntegrable_rpow' hp0:
      IntervalIntegrable (fun t:ℝ=>t^p) volume 0 h).comp_sub_left h).symm
    apply (intervalIntegrable_iff_integrableOn_Ioc_of_le hh.le).mp
    simpa only [sub_zero,sub_self] using hi
  have hDi:IntegrableOn D (Ioc (0:ℝ) h):=
    ((hker.const_mul R).add (hpow.const_mul T)).const_mul K
  have hb':∀t∈Ioo 0 h,|G t|≤D t:=by
    intro t ht
    have hk0:0≤kernel γ s L t:=mul_nonneg (rpow_nonneg ht.1.le _)
      (le_min zero_le_one (rpow_nonneg (mul_nonneg hL.le ht.1.le) _))
    have hw0:0≤(h-t)^p:=rpow_nonneg (by linarith [ht.2]) _
    apply (hb t ht).trans
    apply mul_le_mul_of_nonneg_left _ hK
    by_cases hhalf:t≤h/2
    · have hw:(h-t)^p≤R:=by
        have he:=rpow_le_rpow_of_nonpos (by linarith : (0:ℝ)<h/2)
          (by linarith : h/2≤h-t) hp1
        have heq:(h/2)^p=R:=by
          rw [div_eq_mul_inv,mul_rpow hh.le (by norm_num : (0:ℝ)≤(2:ℝ)⁻¹)]
          dsimp only [R]
          norm_num
          ring
        rwa [heq] at he
      exact (mul_le_mul_of_nonneg_right hw hk0).trans
        (le_add_of_nonneg_right (mul_nonneg hT hw0))
    · have ht2:h/2≤t:=(lt_of_not_ge hhalf).le
      have hk:kernel γ s L t≤T:=by
        have he:=div_le_div_of_nonneg_left (rpow_nonneg hL.le (-γ))
          (by linarith : (0:ℝ)<h/2) ht2
        apply (kernel_cap hγ hs hL ht.1).trans
        apply he.trans_eq
        dsimp only [T]
        ring
      exact (mul_le_mul_of_nonneg_left hk hw0).trans
        (by nlinarith [mul_nonneg hR hk0])
  have hgood:∀ᵐt ∂volume.restrict (Ioc (0:ℝ) h),t∈Ioo 0 h:=by
    filter_upwards [ae_restrict_mem measurableSet_Ioc,ae_restrict_of_ae (volume.ae_ne h)] with t ht hne
    exact ⟨ht.1,lt_of_le_of_ne ht.2 hne⟩
  have hGi:IntegrableOn G (Ioc (0:ℝ) h):=by
    apply hDi.mono' hG.aestronglyMeasurable
    filter_upwards [hgood] with t ht
    simpa only [Real.norm_eq_abs] using hb' t ht
  have hpowint:(∫t in Ioc (0:ℝ) h,(h-t)^p)=h^(p+1)/(p+1):=by
    rw [←intervalIntegral.integral_of_le hh.le,
      intervalIntegral.integral_comp_sub_left (fun t:ℝ=>t^p) h]
    simp only [sub_zero,sub_self]
    rw [integral_rpow (Or.inl hp0),zero_rpow (by linarith : p+1≠0),sub_zero]
  have hkint:(∫t in Ioc (0:ℝ) h,kernel γ s L t)≤(1/γ+1/(s-γ))*L^(-γ):=by
    rw [←PolynomialGaussianTime.integral hγ hs hL]
    apply setIntegral_mono_set (PolynomialGaussianTime.integrable hγ hs hL)
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact mul_nonneg (rpow_nonneg ht.le _) (le_min zero_le_one (rpow_nonneg (mul_nonneg hL.le ht.le) _))
    · exact ae_of_all _ (fun t ht=>ht.1)
  refine ⟨hGi,?_⟩
  have h1:(∫t in Ioc (0:ℝ) h,G t)≤∫t in Ioc (0:ℝ) h,D t:=
    integral_mono_ae hGi hDi (hgood.mono (fun t ht=>(le_abs_self _).trans (hb' t ht)))
  have h2:(∫t in Ioc (0:ℝ) h,D t)=
      K*(R*(∫t in Ioc (0:ℝ) h,kernel γ s L t)+T*(h^(p+1)/(p+1))):=by
    dsimp only [D]
    rw [integral_const_mul,integral_add (hker.const_mul R) (hpow.const_mul T),
      integral_const_mul,integral_const_mul,hpowint]
  rw [h2] at h1
  apply h1.trans
  calc
    _≤K*(R*((1/γ+1/(s-γ))*L^(-γ))+T*(h^(p+1)/(p+1))):=
      mul_le_mul_of_nonneg_left (add_le_add (mul_le_mul_of_nonneg_left hkint hR) le_rfl) hK
    _=_:=by
      rw [rpow_add hh,rpow_one]
      dsimp only [R,T]
      field_simp
      <;> ring

end SHE.PolynomialInitialAgeTime
