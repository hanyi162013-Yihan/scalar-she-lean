module
public import SHE.ScalarHeatRootBands
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace SHE.ScalarHeatBandHolder
open Set MeasureTheory ProbabilityTheory Real GaussianAudit ScalarGaussianSemigroup SmoothCylinders
open scoped NNReal ENNReal

/-- Gaussian heat regularization preserves the original global Holder
constant, independently of every derivative of the smoothed input. -/
theorem heat_holder {a:ℝ→ℝ}(ha:BoundedSmooth a){B K β:ℝ}
    (hB:∀x,|a x|≤B)(hh:∀x y,|a x-a y|≤K*|x-y|^β)(v:ℝ≥0)(x y:ℝ):
    |heat v a x-heat v a y|≤K*|x-y|^β:=by
  have hi(t:ℝ):Integrable (fun z:ℝ=>a (t+z)) (gaussianReal 0 v):=
    (integrable_const B).mono'
      (ha.smooth.continuous.measurable.comp (measurable_const.add measurable_id)).aestronglyMeasurable
      (ae_of_all _ (fun z=>by simpa only [Real.norm_eq_abs] using hB (t+z)))
  have he:heat v a x-heat v a y=∫z:ℝ,a (x+z)-a (y+z) ∂gaussianReal 0 v:=by
    exact (integral_sub (hi x) (hi y)).symm
  rw [he,←Real.norm_eq_abs]
  calc
    _≤∫z:ℝ,‖a (x+z)-a (y+z)‖ ∂gaussianReal 0 v:=norm_integral_le_integral_norm _
    _≤∫_:ℝ,K*|x-y|^β ∂gaussianReal 0 v:=by
      apply integral_mono_ae ((hi x).sub (hi y)).norm (integrable_const _)
      apply ae_of_all
      intro z
      simpa only [Pi.sub_apply,Real.norm_eq_abs,add_sub_add_right_eq_sub] using hh (x+z) (y+z)
    _=_:=by rw [integral_const,probReal_univ,one_smul]

theorem band_bound {a:ℝ→ℝ}(ha:BoundedSmooth a){B:ℝ}
    (hB:∀x,|a x|≤B)(j:ℕ)(x:ℝ):|ScalarHeatBands.band a (j+1) x|≤2*B:=by
  have h1:=heat_bound (ScalarHeatBands.variance (j+1)) hB x
  have h0:=heat_bound (ScalarHeatBands.variance j) hB x
  exact (abs_sub _ _).trans ((add_le_add h1 h0).trans_eq (by ring))

/-- Every actual positive heat band has a global Holder modulus
independent of its frequency and of the smooth companion index. -/
theorem band_holder {a:ℝ→ℝ}(ha:BoundedSmooth a){B K β:ℝ}
    (hB:∀x,|a x|≤B)(hh:∀x y,|a x-a y|≤K*|x-y|^β)(j:ℕ)(x y:ℝ):
    |ScalarHeatBands.band a (j+1) x-ScalarHeatBands.band a (j+1) y|≤(2*K)*|x-y|^β:=by
  have h1:=heat_holder ha hB hh (ScalarHeatBands.variance (j+1)) x y
  have h0:=heat_holder ha hB hh (ScalarHeatBands.variance j) x y
  have he:ScalarHeatBands.band a (j+1) x-ScalarHeatBands.band a (j+1) y=
      (heat (ScalarHeatBands.variance (j+1)) a x-heat (ScalarHeatBands.variance (j+1)) a y)-
        (heat (ScalarHeatBands.variance j) a x-heat (ScalarHeatBands.variance j) a y):=by
    dsimp only [ScalarHeatBands.band,ScalarHeatBands.smooth]
    ring
  rw [he]
  exact (abs_sub _ _).trans ((add_le_add h1 h0).trans_eq (by ring))
end SHE.ScalarHeatBandHolder
