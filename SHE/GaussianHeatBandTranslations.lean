module
public import SHE.ScalarHeatBandCancellation
public import SHE.GaussianTwoPointReserve

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
namespace SHE.GaussianHeatBandTranslations
open Set MeasureTheory ProbabilityTheory Real GaussianAudit SmoothCylinders ScalarGaussianSemigroup
open scoped NNReal ENNReal

def difference(a:ℝ→ℝ)(j:ℕ)(u w t:ℝ):ℝ:=
  ScalarHeatBands.band a (j+1) (t+u)-ScalarHeatBands.band a (j+1) (t+w)

theorem measurable {a:ℝ→ℝ}(ha:BoundedSmooth a)(j:ℕ)(u w:ℝ):
    Measurable (difference a j u w):=by
  have hm:Measurable (ScalarHeatBands.band a (j+1)):=
    (ScalarHeatBands.band_boundedSmooth ha (j+1)).smooth.continuous.measurable
  exact (hm.comp (measurable_id.add_const u)).sub (hm.comp (measurable_id.add_const w))

theorem bounded {a:ℝ→ℝ}{B:ℝ}(hB:∀x,|a x|≤B)(j:ℕ)(u w t:ℝ):
    |difference a j u w t|≤4*B:=by
  have hs(l:ℕ)(z:ℝ):|ScalarHeatBands.smooth a l z|≤B:=heat_bound _ hB z
  have hb(z:ℝ):|ScalarHeatBands.band a (j+1) z|≤2*B:=
    (abs_sub _ _).trans ((add_le_add (hs (j+1) z) (hs j z)).trans_eq (by ring))
  exact (abs_sub _ _).trans ((add_le_add (hb (t+u)) (hb (t+w))).trans_eq (by ring))

/-- Translation differences commute exactly with the scalar Gaussian
reserve, before any two-point bound or actual random data substitution. -/
theorem heat_difference {a:ℝ→ℝ}(ha:BoundedSmooth a)(j:ℕ)(u w x:ℝ)(σ:ℝ≥0):
    heat σ (difference a j u w) x=
      heat σ (ScalarHeatBands.band a (j+1)) (x+u)-
        heat σ (ScalarHeatBands.band a (j+1)) (x+w):=by
  let b:=ScalarHeatBands.band a (j+1)
  obtain ⟨K,hK⟩:=(ScalarHeatBands.band_boundedSmooth ha (j+1)).norm_bound
  have hm:Measurable b:=(ScalarHeatBands.band_boundedSmooth ha (j+1)).smooth.continuous.measurable
  have hi(t:ℝ):Integrable (fun z:ℝ=>b ((x+z)+t)) (gaussianReal 0 σ):=
    (integrable_const K).mono' (hm.comp ((measurable_const.add measurable_id).add_const t)).aestronglyMeasurable
      (ae_of_all _ (fun z=>hK _))
  change (∫z:ℝ,b ((x+z)+u)-b ((x+z)+w) ∂gaussianReal 0 σ)=
    (∫z:ℝ,b ((x+u)+z) ∂gaussianReal 0 σ)-(∫z:ℝ,b ((x+w)+z) ∂gaussianReal 0 σ)
  rw [integral_sub (hi u) (hi w)]
  congr 1 <;> apply integral_congr_ae <;> exact ae_of_all _ (fun z=>by congr 1;ring)

end SHE.GaussianHeatBandTranslations
