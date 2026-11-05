module
public import SHE.GaussianHessianScore
public import SHE.GaussianProfile

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000

namespace SHE.GaussianHolderHessian
open MeasureTheory ProbabilityTheory GaussianAudit GaussianSmooth
open scoped InnerProductSpace NNReal
variable {E:Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Averaging a true directional Hölder modulus preserves its constant. -/
theorem rankOneAverage_holder (ν:Measure E) [IsProbabilityMeasure ν]
    (d:E) {F:E→ℝ} (hF:Measurable F) {M K β:ℝ}
    (hb:∀x,|F x|≤M)
    (hh:∀x s t,|F (x+s • d)-F (x+t • d)|≤K*|s-t|^β) (s t:ℝ):
    |rankOneAverage ν d F s-rankOneAverage ν d F t|≤K*|s-t|^β:=by
  have hi (r:ℝ):Integrable (fun x=>F (x+r • d)) ν:=
    (integrable_const M).mono' (hF.comp (measurable_id.add measurable_const)).aestronglyMeasurable
      (ae_of_all _ (fun x=>by simpa only [Real.norm_eq_abs] using hb (x+r • d)))
  unfold rankOneAverage
  rw [←integral_sub (hi s) (hi t),←Real.norm_eq_abs]
  have h:=norm_integral_le_of_norm_le (μ:=ν) (f:=fun x=>F (x+s • d)-F (x+t • d))
    (integrable_const (K*|s-t|^β)) (ae_of_all _ (fun x=>by
      simpa only [Real.norm_eq_abs] using hh x s t))
  simpa only [integral_const,probReal_univ,one_smul] using h

/-- A centered second score gains the actual directional Hölder
increment of the test. Its constant has no test derivatives. -/
theorem rankOne_secondScore_bound (ν:Measure E) [IsProbabilityMeasure ν]
    (d:E) {F:E→ℝ} (hF:Measurable F) {M K β:ℝ} (hb:∀x,|F x|≤M)
    (hK:0≤K) (hβ:0≤β)
    (hh:∀x s t,|F (x+s • d)-F (x+t • d)|≤K*|s-t|^β)
    (v:ℝ≥0) (hv:0<v):
    |∫z,rankOneAverage ν d F z*secondScore v z ∂gaussianReal 0 v|≤
      K*secondScoreAbsIncrementMoment β*(v:ℝ)^(β/2-1):=by
  have hm:=measurable_rankOneAverage ν d F hF
  have hbound:=rankOneAverage_bound ν d F M hb
  have hholder:=rankOneAverage_holder ν d hF hb hh
  have h:=GaussianProfile.varianceDerivative_holder_bound hm hbound hK hβ
    (show (0:ℝ)<v by exact_mod_cast hv) hholder 0
  unfold GaussianProfile.varianceDerivative at h
  simp only [Real.toNNReal_coe,zero_add,abs_mul,abs_of_pos (by norm_num:(0:ℝ)<1/2)] at h
  nlinarith

/-- Gaussian regression converts the actual Hessian into a centered
one-dimensional second score. A Hölder modulus along the extracted
physical direction gives a genuine fractional variance gain, uniformly
over all complementary covariance degeneracies. -/
theorem covarianceResponse_bound (μ:Measure E) [IsGaussian μ]
    (ℓ:E→L[ℝ]ℝ) (hmean:∫y,ℓ y ∂μ=0) (hvar:0<Var[ℓ;μ])
    {F:E→ℝ} (hF:ContDiff ℝ 2 F) {M A1 A2 K β:ℝ}
    (hb:∀x,‖F x‖≤M) (hD:∀x,‖fderiv ℝ F x‖≤A1)
    (hDD:∀x,‖fderiv ℝ (fderiv ℝ F) x‖≤A2)
    (hK:0≤K) (hβ:0≤β)
    (hh:∀x s t,|F (x+s • normalizedCovarianceResponse μ ℓ)-
      F (x+t • normalizedCovarianceResponse μ ℓ)|≤K*|s-t|^β) (z:E):
    |fderiv ℝ (fderiv ℝ (average μ F)) z (covarianceResponse μ ℓ) (covarianceResponse μ ℓ)|≤
      K*secondScoreAbsIncrementMoment β*Var[ℓ;μ]^(β/2+1):=by
  let d:=normalizedCovarianceResponse μ ℓ
  let v:ℝ≥0:=Var[ℓ;μ].toNNReal
  have hv:(v:ℝ)=Var[ℓ;μ]:=Real.coe_toNNReal _ hvar.le
  have hv0:0<v:=by exact_mod_cast (show (0:ℝ)<v by rw [hv];exact hvar)
  obtain ⟨hLd,ν,hν,hker,hμ⟩:=gaussian_covariance_range_factorization μ ℓ hmean hvar
  letI:IsGaussian ν:=hν
  let Fz:E→ℝ:=fun y=>F (z+y)
  have hFz:Measurable Fz:=hF.continuous.measurable.comp (measurable_const.add measurable_id)
  have hbz:∀y,|Fz y|≤M:=fun y=>by simpa only [Fz,Real.norm_eq_abs] using hb (z+y)
  have hhz:∀x s t,|Fz (x+s • d)-Fz (x+t • d)|≤K*|s-t|^β:=by
    intro x s t
    simpa only [Fz,←add_assoc] using hh (z+x) s t
  have hrank:=rankOne_score_integral ν d v Fz hFz M hbz ℓ hLd hker
    (secondScore v) (by unfold secondScore;fun_prop) (integrable_secondScore v)
  have hscore:(∫y,Fz y*secondScore v (ℓ y) ∂μ)=
      ∫r,rankOneAverage ν d Fz r*secondScore v r ∂gaussianReal 0 v:=by
    exact (congrArg (fun m:Measure E=>∫y,Fz y*secondScore v (ℓ y) ∂m) hμ).trans hrank
  have he:(∫y,F (z+y)*((ℓ y)^2-Var[ℓ;μ]) ∂μ)=
      Var[ℓ;μ]^2*(∫r,rankOneAverage ν d Fz r*secondScore v r ∂gaussianReal 0 v):=by
    rw [←hscore,←integral_const_mul]
    apply integral_congr_ae
    exact ae_of_all _ (fun y=>by
      dsimp only [Fz,secondScore]
      rw [hv]
      field_simp [hvar.ne']
      <;> ring)
  rw [GaussianHessianScore.hessian_average_covarianceResponse_score μ ℓ hmean hvar hF hb hD hDD z,
    he,abs_mul,abs_of_nonneg (sq_nonneg _)]
  have hs:=rankOne_secondScore_bound ν d hFz hbz hK hβ hhz v hv0
  rw [hv] at hs
  have hp:Var[ℓ;μ]^2*Var[ℓ;μ]^(β/2-1)=Var[ℓ;μ]^(β/2+1):=by
    rw [←Real.rpow_natCast,←Real.rpow_add hvar]
    congr 1
    ring
  calc
    _≤Var[ℓ;μ]^2*(K*secondScoreAbsIncrementMoment β*Var[ℓ;μ]^(β/2-1)):=
      mul_le_mul_of_nonneg_left hs (sq_nonneg _)
    _=K*secondScoreAbsIncrementMoment β*Var[ℓ;μ]^(β/2+1):=by
      calc
        _=(K*secondScoreAbsIncrementMoment β)*(Var[ℓ;μ]^2*Var[ℓ;μ]^(β/2-1)):=by ring
        _=_:=by rw [hp]

end SHE.GaussianHolderHessian
