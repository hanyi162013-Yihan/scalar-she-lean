module

public import SHE.NativeMeanScoreKernel

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
noncomputable section

/-! Coarse pointwise native mean-score bound from the actual full history.
This is used only for Fubini domination; the sharp spatial L² estimate
remains the one-input averaging theorem and is not replaced by this bound. -/
namespace SHE.NativeMeanPointBound
open Set MeasureTheory AddCircle Real StoppedFourier StoppedGaussianFeatures
  StoppedGaussianScore StoppedCanonicalScore HeatHistoryScore HeatTorus HeatTorusKernel
  GaussianGramScore GaussianIncrement StoppedMeanEnergy RealHeatCovarianceMean
  MeasurableGaussianScores HeatChristoffelTransfer NativeMeanFields NativeMeanScoreKernel
open scoped InnerProductSpace
local instance : Fact (0<2*Real.pi):=⟨by positivity⟩
variable {n:ℕ}

theorem native_mean_score_point_bound (target:Fin n→ℝ)(a:Fin n→UnitAddCircle)
    (u Λ:ℝ)(hΛ:0<Λ)(t:Fin n→ℝ)(hage:∀i,target i-u=4*π^2*t i)
    (act:∀i,u<target i)(s:ℝ)(hs:0<s)(hmin:∀i,u+s≤target i)
    (c:Domain→ℝ)(hc:Measurable c)(U ell:ℝ)(hcb:∀r,0≤c r ∧ c r≤U)
    (hell:0<ell)(hcl:∀r,ell≤c r)(d:HeatTorus.CircleL2):
    scoreVariance (StoppedGaussianFeatures.stoppedCovariance target target (nativeCenter a) c u)
      (meanDirection (dampedSynthesis target target a u Λ t hage act) d)≤(2/(ell*s))*‖d‖^2:=by
  let v:=weightedFeature target target (nativeCenter a) c hc U hcb (fun _=>le_rfl) u
  let S:=dampedSynthesis target target a u Λ t hage act
  have hrow (z:State n):‖S z‖≤sqrt (2/(ell*s))*‖featureSynthesis v z‖:=by
    have hcE:=(weightedSynthesis_full_history_bounds target target (nativeCenter a) c hc U hcb
      (fun _=>le_rfl) hcl u z).1
    have hcurr:=stopped_damped_current_row_bound Finset.univ (fun i=>(z i:ℂ)) target target
      (nativeCenter a) (fun _ _=>le_rfl) hΛ hs (fun i _=>hmin i)
    have hSn:‖S z‖^2=‖historyG Finset.univ (fun i=>(z i:ℂ)) target target
      (nativeCenter a) Λ u‖^2:=realDamped_norm_sq _ _ _ _ _ _ _ _ z
    apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (sqrt_nonneg _) (norm_nonneg _))).mp
    rw[mul_pow,sq_sqrt (by positivity:0≤2/(ell*s)),hSn]
    have he:=mul_le_mul_of_nonneg_left hcE (show 0≤2/(ell*s) by positivity)
    have he':(2/s)*(fullPhysicalEnergy (historyF Finset.univ (fun i=>(z i:ℂ)) target target
      (nativeCenter a)) u).toReal≤(2/(ell*s))*‖featureSynthesis v z‖^2:=by
      convert! he using 1;field_simp
    exact hcurr.trans he'
  have hr:=(scoreVariance_projection_bound t a S v
    (fun z=>dampedSynthesis_span _ _ _ _ _ _ _ _ z) (sqrt_nonneg _) hrow d).2
  have he:=weightedFeature_gram target target (nativeCenter a) c hc U hcb (fun _=>le_rfl) u
  change Matrix.gram ℝ v=_ at he
  rw[he,sq_sqrt (by positivity:0≤2/(ell*s))] at hr
  exact hr.trans (mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (norm_nonneg _) (Submodule.norm_starProjection_apply_le _ d) 2) (by positivity))

end SHE.NativeMeanPointBound
