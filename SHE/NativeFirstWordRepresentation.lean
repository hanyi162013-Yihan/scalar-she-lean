module

public import SHE.NativeOldLaw

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
noncomputable section

/-! Exact finite Gaussian representation of the n=1 centered word after
the old positive split, retaining the original rough baseline. -/
namespace SHE.NativeFirstWordRepresentation
open Set MeasureTheory ProbabilityTheory Real NativeOldSplit NativeOldLaw GaussianIncrement GaussianAudit
  NativeOldRoot GaussianCovarianceWord NativeGaussianFirstWord ProfileL2
open scoped NNReal InnerProductSpace

theorem coordinate_average {n:ℕ}{A:Matrix (Fin n) (Fin n) ℝ}(hA:A.PosSemidef)(i:Fin n)
    (a:ℝ→ℝ)(ha:Measurable a)(m:ℝ):
    (∫y:State n,a (m+y i) ∂multivariateGaussian 0 A)=
      ∫z,a (m+z) ∂gaussianReal 0 (A i i).toNNReal:=by
  have hp:=measurePreserving_eval_multivariateGaussian (μ:=(0:State n)) hA (i:=i)
  have hLaw:HasLaw (fun y:State n=>y i) (gaussianReal 0 (A i i).toNNReal) (multivariateGaussian 0 A):=
    ⟨hp.measurable.aemeasurable,by simpa only[PiLp.zero_apply] using hp.map_eq⟩
  exact hLaw.integral_comp (f:=fun z=>a (m+z))
    ((ha.comp (measurable_const.add measurable_id)).aestronglyMeasurable)

/-- The old fraction changes only the root covariance. The newest rough
baseline is exactly the same under the full and residual Gaussian laws. -/
theorem newest_baseline_unchanged {A:Matrix (Fin 2) (Fin 2) ℝ}(hA:A.PosSemidef)
    (v:ℝ≥0)(a:ℝ→ℝ)(ha:Measurable a)(m:State 2):
    GaussianCovarianceWord.average (A+rootCovariance v) (fun y=>a (y 1)) m=
      GaussianCovarianceWord.average A (fun y=>a (y 1)) m:=by
  have hB: (A+rootCovariance (v:ℝ)).PosSemidef:=hA.add (rootCovariance_positive v.coe_nonneg)
  change (∫y:State 2,a ((m+y) 1) ∂multivariateGaussian 0 (A+rootCovariance v))=
    ∫y:State 2,a ((m+y) 1) ∂multivariateGaussian 0 A
  simp only[PiLp.add_apply]
  rw[coordinate_average hB 1 a ha,coordinate_average hA 1 a ha]
  simp[rootCovariance,Matrix.add_apply]

/-- Exact nested old-score representation of the centered complete n=1
word, with its baseline computed from the TOTAL original Gaussian law. -/
theorem firstWord_nested_old_score {A:Matrix (Fin 2) (Fin 2) ℝ}(hA:A.PosSemidef)
    (v:ℝ≥0)(f f' a:ℝ→ℝ)(A0 ν M:ℝ)(hA0:0≤A0)(hν:0≤ν)
    (hf:∀z,HasDerivAt f (f' z) z)(hfb:∀z,|f z|≤A0)(hfD:∀z,|f' z|≤A0*ν)
    (ha:Measurable a)(haB:∀z,|a z|≤M)(m:State 2):
    (∫y:State 2,(∫z:ℝ,GaussianAudit.secondScore v z*f ((m+y) 0+z)*
        (a ((m+y) 1)-GaussianCovarianceWord.average (A+rootCovariance v) (fun w=>a (w 1)) m)
        ∂gaussianReal 0 v) ∂multivariateGaussian 0 A)=
      firstWord A v f a (EuclideanSpace.proj 0) (EuclideanSpace.proj 1) m:=by
  rw[newest_baseline_unchanged hA v a ha m]
  have hfc:Continuous f:=continuous_iff_continuousAt.mpr (fun z=>(hf z).continuousAt)
  let b:State 2→ℝ:=fun y=>oldRoot v f (y 0)
  let aL:State 2→ℝ:=fun y=>a (y 1)
  let B:=2*A0*rootClipMass v ν
  have hb:Measurable b:=(oldRoot_measurable v f hfc).comp (by fun_prop)
  have ham:Measurable aL:=by fun_prop
  have hbb:∀y,|b y|≤B:=fun y=>oldRoot_clipped_bound v f f' hA0 hν hf hfb hfD (y 0)
  have hbm:MemLp (fun y=>b (m+y)) 2 (multivariateGaussian 0 A):=
    bounded_memLp (by fun_prop) (fun _=>hbb _)
  have hamL:MemLp (fun y=>aL (m+y)) 2 (multivariateGaussian 0 A):=
    bounded_memLp (by fun_prop) (fun _=>haB _)
  calc
    _=∫y:State 2,b (m+y)*(aL (m+y)-GaussianCovarianceWord.average A aL m) ∂multivariateGaussian 0 A:=by
      apply integral_congr_ae
      exact ae_of_all _ (fun y=>by
        change (∫z:ℝ,GaussianAudit.secondScore v z*f ((m+y) 0+z)*
          (a ((m+y) 1)-GaussianCovarianceWord.average A (fun w=>a (w 1)) m) ∂gaussianReal 0 v)=_
        rw[integral_mul_const]
        rfl)
    _=firstWord A v f a (EuclideanSpace.proj 0) (EuclideanSpace.proj 1) m:=by
      simp_rw[mul_sub]
      have hip:Integrable (fun y=>b (m+y)*aL (m+y)) (multivariateGaussian 0 A):=
        hbm.integrable_mul hamL
      rw[integral_sub hip ((hbm.integrable one_le_two).mul_const _),integral_mul_const]
      rfl

end SHE.NativeFirstWordRepresentation
