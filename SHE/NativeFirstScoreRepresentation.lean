module
public import SHE.NativeFirstScoreReserve
public import SHE.GaussianFixedFirstAverage
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
namespace SHE.NativeFirstScoreRepresentation
open MeasureTheory ProbabilityTheory GaussianIncrement GaussianConvolution ControlledProfile StoppedFourier
  StoppedGaussianFeatures StoppedGaussianScore PhysicalMeanRange
local instance : Fact (0<2*Real.pi):=⟨by positivity⟩
variable {X:Type*} [MeasurableSpace X] {n:ℕ}

/-- The remaining covariance after inserting a fixed native fraction
is genuinely positive, with the original stopped observation geometry. -/
theorem residual_posSemidef (P:CanonicalCovariance.ProfileParameters)(Λ:ℝ)(u d:CircleL2)
    (old:ControlledProfile.Domain→ℝ)(hold:Measurable old)(holdb:∀p,0≤old p ∧ old p≤P.lower/2)
    (σ target:Fin n→ℝ)(center:Fin n→HeatCircle)(hages:∀i,σ i≤target i)(q θ:ℝ):
    (ControlledFixedReserve.covariance P Λ u d (NativeFirstScoreReserve.oldProfile P old) σ target center q θ).PosSemidef:=by
  have hm:Measurable (ControlledFixedReserve.coefficient P Λ u d (NativeFirstScoreReserve.oldProfile P old) θ):=
    ((ControlledProfile.profile_measurable P Λ u d).comp (measurable_const.prodMk measurable_id)).sub
      (NativeFirstScoreReserve.oldProfile_measurable P hold)
  exact StoppedCovarianceSplit.covariance_posSemidef σ target center hages q hm (fun p=>
    ⟨(by have := P.lower_pos; positivity:0≤3*P.lower/8).trans
      (NativeFirstScoreReserve.residual_bounds P Λ u d holdb θ p).1,
      (NativeFirstScoreReserve.residual_bounds P Λ u d holdb θ p).2⟩)

/-- Every actual undamped native input direction lies in the FIXED
first-score covariance range, including colliding observations. -/
theorem current_range (P:CanonicalCovariance.ProfileParameters)
    (σ target:Fin n→ℝ)(center:Fin n→UnitAddCircle)(q:ℝ)
    (hgap:∀i,q<σ i)(hages:∀i,σ i≤target i)(f:CircleL2):
    currentDirection target center q f∈(Matrix.toEuclideanCLM (𝕜:=ℝ)
      (NativeFirstScoreReserve.covariance P σ target (nativeCenter center) q)).range:=by
  obtain ⟨δ,hδ,hstop⟩:=exists_positive_gap (fun i=>σ i-q) (fun i=>sub_pos.mpr (hgap i))
  exact currentDirection_mem_range σ target center q hages δ hδ (fun i=>by linarith [hstop i])
    (fun _=>NativeFirstScoreReserve.floor P) measurable_const (NativeFirstScoreReserve.floor P)
    (NativeFirstScoreReserve.floor P) (fun _=>⟨by have := P.lower_pos; dsimp [NativeFirstScoreReserve.floor];positivity,le_rfl⟩)
    (by have := P.lower_pos; dsimp [NativeFirstScoreReserve.floor];positivity) (fun _=>le_rfl) f

/-- Exact directional derivative of the ORIGINAL controlled covariance
kernel, represented by the smaller residual law and an unchanged
independent native first score. No smoothness of the whole test is assumed. -/
theorem derivative (P:CanonicalCovariance.ProfileParameters)(Λ:ℝ)(u d:CircleL2)
    (old:ControlledProfile.Domain→ℝ)(hold:Measurable old)(holdb:∀p,0≤old p ∧ old p≤P.lower/2)
    (σ target:Fin n→ℝ)(center:Fin n→HeatCircle)(hσ:∀i,0<σ i)(hσ1:∀i,σ i≤1)
    (hages:∀i,σ i≤target i)(q:ℝ)(hq:0≤q)(θ:ℝ)(e:State n)
    (he:e∈(Matrix.toEuclideanCLM (𝕜:=ℝ) (NativeFirstScoreReserve.covariance P σ target center q)).range)
    (μ:Measure X) [SFinite μ](w:X→ℝ)(hw:Integrable w μ)(hwm:Measurable w)
    (shift:X→State n)(hs:Measurable shift)(F:State n→ℝ)(hF:Measurable F)
    (M:ℝ)(hM:0≤M)(hb:∀z,|F z|≤M)(z:State n):
    deriv (fun t:ℝ=>gaussianAverage (ControlledFixedReserve.covariance P Λ u d old σ target center q θ)
      (WeightedBorelAverage.average μ w shift F) (z+t•e)) 0=
    gaussianAverage (ControlledFixedReserve.covariance P Λ u d (NativeFirstScoreReserve.oldProfile P old) σ target center q θ)
      (WeightedBorelAverage.average (μ.prod (multivariateGaussian 0 (NativeFirstScoreReserve.covariance P σ target center q)))
        (GaussianFixedFirstAverage.weight (NativeFirstScoreReserve.covariance P σ target center q) e w)
        (GaussianFixedFirstAverage.shift shift) F) z:=by
  have hh:=GaussianFixedFirstAverage.hasDerivAt μ
    (NativeFirstScoreReserve.covariance_posSemidef P σ target center hages q)
    (residual_posSemidef P Λ u d old hold holdb σ target center hages q θ) he
    w hw hwm shift hs F hF M hM hb z 0
  rw [NativeFirstScoreReserve.covariance_split P Λ u d hold holdb σ target center hσ hσ1 hages q hq θ] at hh
  simpa only [zero_smul,add_zero] using hh.deriv
end SHE.NativeFirstScoreRepresentation
