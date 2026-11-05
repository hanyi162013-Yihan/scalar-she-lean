module

public import SHE.GaussianAudit
public import SHE.FiniteDifferences

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section

/-! The actual centered old Gaussian second-score/root factor of the first
word, with a proved clipped Bernstein increment mass. -/
namespace SHE.NativeOldRoot
open Set MeasureTheory ProbabilityTheory GaussianAudit FiniteDifferences Real
open scoped NNReal

/-- No variance or direction is hidden in this root factor. -/
def oldRoot (v: ℝ≥0) (f:ℝ→ℝ) (m:ℝ):ℝ:=
  ∫z,GaussianAudit.secondScore v z*f (m+z) ∂gaussianReal 0 v

def rootClipMass (v: ℝ≥0) (ν:ℝ):ℝ:=
  ∫z,|GaussianAudit.secondScore v z| *min 1 (ν*|z|) ∂gaussianReal 0 v

def rootClipConstant:ℝ:=max (secondScoreAbsIncrementMoment 0) (secondScoreAbsIncrementMoment 1)

theorem rootClipConstant_nonneg:0≤rootClipConstant:=by
  apply le_trans _ (le_max_left _ _)
  exact integral_nonneg (fun z=>mul_nonneg (abs_nonneg _) (rpow_nonneg (abs_nonneg _) _))

theorem integrable_rootClipMass (v: ℝ≥0) {ν:ℝ} (hν:0≤ν):
    Integrable (fun z=>|GaussianAudit.secondScore v z| *min 1 (ν*|z|)) (gaussianReal 0 v):=by
  apply (integrable_secondScore v).norm.mul_bdd (c:=1)
  · exact (continuous_const.min (continuous_const.mul continuous_abs)).aestronglyMeasurable
  · exact ae_of_all _ (fun z=>by
      rw[Real.norm_eq_abs,abs_of_nonneg (le_min (by norm_num) (mul_nonneg hν (abs_nonneg z)))]
      exact min_le_left _ _)

theorem rootClipMass_nonneg (v: ℝ≥0) {ν:ℝ} (hν:0≤ν):0≤rootClipMass v ν:=
  integral_nonneg (fun z=>mul_nonneg (abs_nonneg _) (le_min (by norm_num) (mul_nonneg hν (abs_nonneg z))))

theorem oldRoot_measurable (v: ℝ≥0) (f:ℝ→ℝ) (hf:Continuous f):Measurable (oldRoot v f):=by
  have hm:Measurable (fun p:ℝ×ℝ=>GaussianAudit.secondScore v p.2*f (p.1+p.2)):=by
    unfold GaussianAudit.secondScore
    fun_prop
  exact hm.stronglyMeasurable.integral_prod_right'.measurable

theorem oldRoot_centered (v: ℝ≥0) (f:ℝ→ℝ) (hf:Continuous f) (A:ℝ) (hA:∀x,|f x|≤A) (m:ℝ):
    oldRoot v f m=∫z,GaussianAudit.secondScore v z*(f (m+z)-f m) ∂gaussianReal 0 v:=by
  exact (secondScore_center_root v f m (integrable_secondScore_root v f m A hf hA)).symm

theorem oldRoot_clipped_bound (v: ℝ≥0) (f f':ℝ→ℝ) {A ν:ℝ} (hA:0≤A) (hν:0≤ν)
    (hf:∀x,HasDerivAt f (f' x) x) (hb:∀x,|f x|≤A) (hd:∀x,|f' x|≤A*ν) (m:ℝ):
    |oldRoot v f m|≤2*A*rootClipMass v ν:=by
  have hfc:Continuous f:=continuous_iff_continuousAt.mpr (fun x=>(hf x).continuousAt)
  have hidiff : Integrable (fun z=>GaussianAudit.secondScore v z*(f (m+z)-f m)) (gaussianReal 0 v) := by
    convert! (integrable_secondScore_root v f m A hfc hb).sub
      ((integrable_secondScore v).mul_const (f m)) using 1
    funext z
    change GaussianAudit.secondScore v z*(f (m+z)-f m)=
      GaussianAudit.secondScore v z*f (m+z)-GaussianAudit.secondScore v z*f m
    ring
  rw[oldRoot_centered v f hfc A hb m,←Real.norm_eq_abs]
  calc
    _≤∫z,‖GaussianAudit.secondScore v z*(f (m+z)-f m)‖ ∂gaussianReal 0 v:=norm_integral_le_integral_norm _
    _≤∫z,2*A*(|GaussianAudit.secondScore v z| *min 1 (ν*|z|)) ∂gaussianReal 0 v:=by
      apply integral_mono
        hidiff.norm
        ((integrable_rootClipMass v hν).const_mul (2*A))
      intro z
      change ‖GaussianAudit.secondScore v z*(f (m+z)-f m)‖≤2*A*(|GaussianAudit.secondScore v z| * min 1 (ν*|z|))
      rw[Real.norm_eq_abs,abs_mul]
      have hh:=difference_clipped_bound hA hν hf hb hd z m
      change |f (m+z)-f m|≤_ at hh
      nlinarith [abs_nonneg (GaussianAudit.secondScore v z)]
    _=2*A*rootClipMass v ν:=integral_const_mul _ _

theorem rootClipMass_scaled_bound {v: ℝ≥0} (hv:v≠0) {ν:ℝ} (hν:0≤ν):
    rootClipMass v ν≤(rootClipConstant/(v:ℝ))*min 1 (ν*sqrt (v:ℝ)):=by
  have hvp:0<(v:ℝ):=by exact_mod_cast (pos_iff_ne_zero.mpr hv)
  have hlarge:rootClipMass v ν≤secondScoreAbsIncrementMoment 0/(v:ℝ):=by
    have hi:Integrable (fun z=>|GaussianAudit.secondScore v z|) (gaussianReal 0 v):=(integrable_secondScore v).norm
    calc
      _≤∫z,|GaussianAudit.secondScore v z| ∂gaussianReal 0 v:=
        integral_mono (integrable_rootClipMass v hν) hi (fun z=>mul_le_of_le_one_right (abs_nonneg _) (min_le_left _ _))
      _=secondScoreAbsIncrementMoment 0/(v:ℝ):=by
        have hh:=secondScore_abs_increment_moment v hv 0 (by norm_num)
        simpa only[zero_div,zero_mul,rpow_zero,mul_one,one_mul,one_div,div_eq_mul_inv,mul_comm] using hh
  have hsmall:rootClipMass v ν≤ν*(sqrt (v:ℝ)/(v:ℝ))*secondScoreAbsIncrementMoment 1:=by
    have hi:=integrable_secondScore_abs_rpow v 1 (by norm_num)
    calc
      _≤∫z,ν*(|GaussianAudit.secondScore v z| *|z|^(1:ℝ)) ∂gaussianReal 0 v:=by
        apply integral_mono (integrable_rootClipMass v hν) (hi.const_mul ν)
        intro z
        change |GaussianAudit.secondScore v z| * min 1 (ν*|z|) ≤ ν*(|GaussianAudit.secondScore v z| * |z|^(1:ℝ))
        rw[rpow_one]
        have hh:=mul_le_mul_of_nonneg_left (min_le_right 1 (ν*|z|)) (abs_nonneg (GaussianAudit.secondScore v z))
        nlinarith
      _=ν*(sqrt (v:ℝ)/(v:ℝ))*secondScoreAbsIncrementMoment 1:=by
        rw[integral_const_mul,secondScore_abs_increment_moment v hv 1 (by norm_num),
          Real.rpow_div_two_eq_sqrt (1:ℝ) v.coe_nonneg]
        simp only [rpow_one]
        ring
  by_cases hsmallclip:ν*sqrt (v:ℝ)≤1
  · rw[min_eq_right hsmallclip]
    calc
      _≤ν*(sqrt (v:ℝ)/(v:ℝ))*secondScoreAbsIncrementMoment 1:=hsmall
      _≤ν*(sqrt (v:ℝ)/(v:ℝ))*rootClipConstant:=
        mul_le_mul_of_nonneg_left (le_max_right _ _) (by positivity)
      _=_:=by ring
  · rw[min_eq_left (le_of_not_ge hsmallclip),mul_one]
    exact hlarge.trans (div_le_div_of_nonneg_right (le_max_left _ _) hvp.le)

end SHE.NativeOldRoot
