module

public import SHE.ScalarGaussianSemigroup

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2300000
namespace SHE.ScalarGaussianJetScale
open Set MeasureTheory ProbabilityTheory Filter Topology Real GaussianAudit GaussianSmooth SmoothCylinders ScalarGaussianSemigroup
open scoped NNReal ENNReal

/-- The true first derivative of a bounded Gaussian average has its
variance^{-1/2} scale, with an actual finite standard Gaussian moment. -/
theorem first_bound (v : ℝ≥0) (hv : v≠0) {a : ℝ→ℝ} (ha : Measurable a) {B : ℝ}
    (hB : ∀ x,|a x|≤B) (x : ℝ) :
    |deriv (heat v a) x|≤B*gaussianAbsMoment 1*(v:ℝ)^(-(1/2:ℝ)) := by
  have hvp : 0<(v:ℝ):=by exact_mod_cast (pos_iff_ne_zero.mpr hv)
  have hi : Integrable (fun z=>a (x+z)*firstScore v z) (gaussianReal 0 v):=
    (integrable_firstScore v).bdd_mul (ha.comp (measurable_const.add measurable_id)).aestronglyMeasurable
      (ae_of_all _ (fun z=>by simpa only [Real.norm_eq_abs] using hB (x+z)))
  rw [(hasDerivAt_gaussianConvolution v hv a ha B hB x).deriv,←Real.norm_eq_abs]
  calc
    _≤∫ z,‖a (x+z)*firstScore v z‖ ∂gaussianReal 0 v:=norm_integral_le_integral_norm _
    _≤∫ z,B*(|z|^(1:ℝ)/(v:ℝ)) ∂gaussianReal 0 v:=by
      apply integral_mono_ae hi.norm (((integrable_gaussian_abs_rpow v 1 (by norm_num)).div_const (v:ℝ)).const_mul B)
      exact ae_of_all _ (fun z=>by
        change ‖a (x+z)*firstScore v z‖≤B*(|z|^(1:ℝ)/(v:ℝ))
        rw [Real.norm_eq_abs,abs_mul,firstScore,abs_div,abs_of_pos hvp,Real.rpow_one]
        exact mul_le_mul_of_nonneg_right (hB (x+z)) (div_nonneg (abs_nonneg _) hvp.le))
    _=B*gaussianAbsMoment 1*(v:ℝ)^(-(1/2:ℝ)):=by
      rw [integral_const_mul,integral_div,gaussian_abs_rpow_moment v 1 (by norm_num)]
      have he : (v:ℝ)^((1:ℝ)/2)/(v:ℝ)=(v:ℝ)^(-(1/2:ℝ)):=by
        rw [←Real.rpow_sub_one hvp.ne']
        congr 1
        norm_num
      calc
        _=B*gaussianAbsMoment 1*((v:ℝ)^((1:ℝ)/2)/(v:ℝ)):=by ring
        _=_:=by rw [he]

def constant (β : ℝ) : ℕ→ℝ
  | 0=>gaussianAbsMoment (β+1)
  | n+1=>gaussianAbsMoment 1*constant β n*2^(((n:ℝ)+2-β)/2)

theorem constant_nonneg (β : ℝ) (n : ℕ) : 0≤constant β n:=by
  induction n with
  | zero => exact gaussianAbsMoment_nonneg _
  | succ n ih => exact mul_nonneg (mul_nonneg (gaussianAbsMoment_nonneg _) ih) (by positivity)

/-- All positive Gaussian smoothing derivatives of an ACTUAL smooth
Holder test have rough coefficient constants, independent of every
unsmoothed derivative. Order n+1 has exact variance^(beta-n-1)/2. -/
theorem jet_holder (v : ℝ≥0) (hv : v≠0) {a : ℝ→ℝ} (ha : BoundedSmooth a)
    {H β : ℝ} (hH : 0≤H) (hβ : 0≤β)
    (hh : ∀ x y,|a x-a y|≤H*|x-y|^β) (n : ℕ) (x : ℝ) :
    |iteratedDeriv (n+1) (heat v a) x|≤H*constant β n*(v:ℝ)^((β-(n:ℝ)-1)/2) := by
  obtain ⟨B,hBn⟩:=ha.norm_bound
  have hB (z : ℝ) : |a z|≤B:=by simpa only [Real.norm_eq_abs] using hBn z
  induction n generalizing v x with
  | zero =>
    obtain ⟨B,hB⟩:=ha.norm_bound
    simpa only [Nat.zero_add,iteratedDeriv_one,constant,Nat.cast_zero,sub_zero] using
      GaussianProfileMean.gaussian_mean_derivative_holder_bound v hv a ha.smooth.continuous.measurable B
        (fun z=>by simpa only [Real.norm_eq_abs] using hB z) hβ hH hh x
  | succ n ih =>
    let w : ℝ≥0:=v/2
    have hw : w≠0:=div_ne_zero hv (by norm_num)
    have hwpos : 0<(w:ℝ):=by exact_mod_cast (pos_iff_ne_zero.mpr hw)
    have hvpos : 0<(v:ℝ):=by exact_mod_cast (pos_iff_ne_zero.mpr hv)
    have hww : w+w=v:=by dsimp only [w]; ring
    have he : iteratedDeriv ((n+1)+1) (heat v a)=
        deriv (heat w (iteratedDeriv (n+1) (heat w a))) := by
      rw [iteratedDeriv_succ,←hww,←heat_heat w w ha.smooth.continuous.measurable
        hB]
      rw [iteratedDeriv_heat w (heat_boundedSmooth w ha) (n+1)]
    rw [show n+1+1=(n+1)+1 by omega,he]
    have hb (z : ℝ) : |iteratedDeriv (n+1) (heat w a) z|≤
        H*constant β n*(w:ℝ)^((β-(n:ℝ)-1)/2):=ih w hw z
    have hs:=first_bound w hw (iteratedDeriv_boundedSmooth (heat_boundedSmooth w ha) (n+1)).smooth.continuous.measurable hb x
    apply hs.trans_eq
    have hp : (w:ℝ)^((β-(n:ℝ)-1)/2)*(w:ℝ)^(-(1/2:ℝ))=
        (v:ℝ)^((β-(n:ℝ)-2)/2)*2^(((n:ℝ)+2-β)/2) := by
      rw [←Real.rpow_add hwpos]
      rw [show (w:ℝ)=(v:ℝ)/2 by rfl,Real.div_rpow hvpos.le (by norm_num)]
      rw [div_eq_mul_inv,←Real.rpow_neg (by norm_num : 0≤(2:ℝ))]
      congr 1 <;> ring
    simp only [constant,Nat.cast_add,Nat.cast_one]
    calc
      _=H*(gaussianAbsMoment 1*constant β n)*
          ((w:ℝ)^((β-(n:ℝ)-1)/2)*(w:ℝ)^(-(1/2:ℝ))):=by ring
      _=_:=by rw [hp]; ring

end SHE.ScalarGaussianJetScale
