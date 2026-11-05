module
public import SHE.GaussianHolderHessian
public import SHE.FixedOldHessianBound

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1700000

namespace SHE.GaussianHolderScore
open MeasureTheory ProbabilityTheory GaussianAudit GaussianSmooth
open scoped InnerProductSpace NNReal
variable {E:Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- The fresh second-score Hölder gain only needs a bounded measurable
test. The old fixed Gaussian score average is therefore admissible. -/
theorem centered_square_bound (μ:Measure E) [IsGaussian μ]
    (ℓ:E→L[ℝ]ℝ) (hmean:∫y,ℓ y ∂μ=0) (hvar:0<Var[ℓ;μ])
    {F:E→ℝ} (hF:Measurable F) {M K β:ℝ} (hb:∀x,|F x|≤M)
    (hK:0≤K) (hβ:0≤β)
    (hh:∀x s t,|F (x+s • normalizedCovarianceResponse μ ℓ)-
      F (x+t • normalizedCovarianceResponse μ ℓ)|≤K*|s-t|^β) (z:E):
    |∫y,F (z+y)*((ℓ y)^2-Var[ℓ;μ]) ∂μ|≤
      K*secondScoreAbsIncrementMoment β*Var[ℓ;μ]^(β/2+1):=by
  let d:=normalizedCovarianceResponse μ ℓ
  let v:ℝ≥0:=Var[ℓ;μ].toNNReal
  have hv:(v:ℝ)=Var[ℓ;μ]:=Real.coe_toNNReal _ hvar.le
  have hv0:0<v:=by exact_mod_cast (show (0:ℝ)<v by rw [hv];exact hvar)
  obtain ⟨hLd,ν,hν,hker,hμ⟩:=gaussian_covariance_range_factorization μ ℓ hmean hvar
  letI:IsGaussian ν:=hν
  let Fz:E→ℝ:=fun y=>F (z+y)
  have hFz:Measurable Fz:=hF.comp (measurable_const.add measurable_id)
  have hbz:∀y,|Fz y|≤M:=fun y=>hb (z+y)
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
      field_simp [hvar.ne'])
  rw [he,abs_mul,abs_of_nonneg (sq_nonneg _)]
  have hs:=GaussianHolderHessian.rankOne_secondScore_bound ν d hFz hbz hK hβ hhz v hv0
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

end SHE.GaussianHolderScore
