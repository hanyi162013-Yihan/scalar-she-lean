module

public import SHE.NativeFirstWordMeanPower
public import SHE.NativeMeanPointBound

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
noncomputable section

/-! A coarse actual pointwise envelope for time Fubini of the n=1 mean
word. This envelope is never substituted for the sharp signed-input L²
power proved by NativeFirstWordMeanPower. -/
namespace SHE.NativeMeanWordDomination
open Set MeasureTheory ProbabilityTheory AddCircle Real StoppedFourier StoppedGaussianFeatures
  StoppedGaussianScore HeatHistoryScore HeatTorus HeatTorusKernel GaussianGramScore GaussianIncrement
  MeasurableGaussianScores NativeMeanFields NativeMeanScoreKernel MeasurableGeneralizedInverse
  GaussianWordFields NativeGaussianFirstWord GaussianAudit NativeOldRoot NativeFirstWordMeanTree
  NativeFirstWordMeanPower GaussianWordMeanDerivative NativeMeanPointBound
  ProfileVariance OldFractionHeatScale FirstWordPowers ProfileL2 StoppedGaussianMarginals
  HeatTreeAveraging
open scoped InnerProductSpace NNReal
local instance : Fact (0<2*Real.pi):=⟨by positivity⟩

/-- The literal finite-gap native word has a coarse pointwise envelope with
integrable newest time degree (β-2)/4. Its sole use is domination. -/
theorem native_mean_word_point_bound
    (target:Fin 2→ℝ)(ht1:∀i,target i≤1)(Λ:ℝ)(hΛ:0<Λ)
    (t:Fin 2→ℝ)(_ht:∀i,0<t i)(hage:∀i,target i=4*π^2*t i)
    (s:ℝ)(hs:0<s)(hmin:∀i,s≤target i)(hleaf:target 1=s)
    (c:(UnitAddCircle×UnitAddCircle)×Domain→ℝ)(hc:Measurable c)(U ell:ℝ)
    (hcb:∀p r,0≤c (p,r) ∧ c (p,r)≤U)(hell:0<ell)(hcl:∀p r,ell≤c (p,r))
    (d:HeatTorus.CircleL2)(m:UnitAddCircle×UnitAddCircle→State 2)
    (r ellOld:ℝ)(hr:0<r)(hr1:r≤1)(hellOld:0<ellOld)
    (f f' b:ℝ→ℝ)(A0 ν M H β:ℝ)
    (hA0:0≤A0)(hν:0≤ν)(hf:∀z,HasDerivAt f (f' z) z)(hfb:∀z,|f z|≤A0)(hfD:∀z,|f' z|≤A0*ν)
    (hb:Measurable b)(hbB:∀z,|b z|≤M)(hH:0≤H)(hβ:0≤β)(hholder:∀z w,|b z-b w|≤H*|z-w|^β)
    (x:UnitAddCircle):
    let act:∀i,0<target i:=fun i=>hs.trans_le (hmin i)
    let F:=meanDerivativeField target Λ t hage act c d m (oldVariance ellOld r) f b
    |∫y,‖HeatMarkov.kernel (r/(4*π^2)) (by positivity) y‖^2*F (y,x) ∂haarAddCircle|≤
      4*A0*rootScaleConstant ellOld*roughConstant U H β*sqrt (2/ell)*
        SHE.rootKernel ν r*s^((β-2)/4)*‖d‖:=by
  intro act F
  let A:=covarianceField target NativeFirstWordMeanTree.relativeCenters c 0
  let D:=directionField target NativeFirstWordMeanTree.relativeCenters 0 Λ t (fun i=>by simpa using hage i) act (fun _=>d)
  let T:=4*A0*rootClipMass (oldVariance ellOld r) ν*
    sqrt (H^2*(upperConstant*U*s^(1/2:ℝ))^β*gaussianAbsMoment (2*β))
  have hU:0≤U:=(hcb (0,0) (0,0)).1.trans (hcb (0,0) (0,0)).2
  have hF (y:UnitAddCircle):|F (y,x)|≤T*sqrt (2/(ell*s))*‖d‖:=by
    let p:UnitAddCircle×UnitAddCircle:=(y,x)
    have hA:(A p).PosSemidef:=StoppedGaussianFields.covariance_posSemidef
      (NativeMeanFields.observations target NativeFirstWordMeanTree.relativeCenters
        NativeFirstWordMeanTree.relativeCenters_measurable) c (fun _=>0) p
      (hc.comp (measurable_const.prodMk measurable_id)) (hcb p) (fun _=>le_rfl)
    have hDr:D p∈(Matrix.toEuclideanCLM (𝕜:=ℝ) (A p)).range:=
      physical_mean_direction_mem_range target (fun i=>NativeFirstWordMeanTree.relativeCenters p.1 i+p.2)
        0 Λ hΛ t (fun i=>by simpa using hage i) act s hs (fun i=>by simpa using hmin i)
        (fun z=>c (p,z)) (hc.comp (measurable_const.prodMk measurable_id)) U ell (hcb p) hell (hcl p) d
    have hW:Var[EuclideanSpace.proj (𝕜:=ℝ) (1:Fin 2);multivariateGaussian 0 (A p)]≤
        upperConstant*U*s^(1/2:ℝ):=by
      have hh:=native_coordinate_variance_bound target
        (nativeCenter (fun i=>NativeFirstWordMeanTree.relativeCenters p.1 i+p.2)) act ht1
        (fun z=>c (p,z)) (hc.comp (measurable_const.prodMk measurable_id)) U (hcb p) 1
      convert! hh using 1
      rw[hleaf]
    have hh:=firstMeanScore_bound hA hDr (oldVariance ellOld r) f f' b
      (EuclideanSpace.proj 0) (EuclideanSpace.proj 1) A0 ν M H β
      (upperConstant*U*s^(1/2:ℝ)) hA0 hν hf hfb hfD hb hbB hH hβ hholder hW (m p)
    have hp:=native_mean_score_point_bound target
      (fun i=>NativeFirstWordMeanTree.relativeCenters p.1 i+p.2) 0 Λ hΛ t
      (fun i=>by simpa using hage i) act s hs (fun i=>by simpa using hmin i)
      (fun z=>c (p,z)) (hc.comp (measurable_const.prodMk measurable_id)) U ell (hcb p) hell (hcl p) d
    have hsqrt:sqrt (scoreVariance (A p) (D p))≤sqrt (2/(ell*s))*‖d‖:=by
      have hh:=sqrt_le_sqrt hp
      rw[sqrt_mul (by positivity:0≤2/(ell*s)),sqrt_sq (norm_nonneg d)] at hh
      exact hh
    convert! hh.trans (mul_le_mul_of_nonneg_left hsqrt (by
      positivity [rootClipMass_nonneg (oldVariance ellOld r) hν])) using 1
    ring
  have hh:=norm_integral_le_of_norm_le_const (μ:=heatSquareMeasure (r/(4*π^2)) (by positivity))
    (f:=fun y=>F (y,x)) (C:=T*sqrt (2/(ell*s))*‖d‖)
    (ae_of_all _ (fun y=>by simpa only[Real.norm_eq_abs] using hF y))
  rw[integral_heatSquareMeasure,heatSquareMeasure_mass,Real.norm_eq_abs] at hh
  have hrough:=rough_gain_identity hs hU H β
  have htime:s^(β/4)*sqrt (2/(ell*s))=sqrt (2/ell)*s^((β-2)/4):=by
    have he:sqrt (2/(ell*s))=sqrt (2/ell)*(sqrt s)⁻¹:=by
      rw[show 2/(ell*s)=(2/ell)/s by ring,sqrt_div (by positivity:0≤2/ell)]
      rfl
    rw[he,Real.sqrt_eq_rpow s,←Real.rpow_neg hs.le]
    calc
      _=sqrt (2/ell)*(s^(β/4)*s^(-(1/2:ℝ))):=by ring
      _=_:=by rw[←Real.rpow_add hs];congr 2;ring
  have hroot:=old_fraction_heat_root_bound hellOld hr hr1 hν
  have he:‖unitHeatKernel (r/(4*π^2)) 0‖^2*(T*sqrt (2/(ell*s))*‖d‖)=
      (4*A0*roughConstant U H β*sqrt (2/ell)*s^((β-2)/4)*‖d‖)*
      (‖unitHeatKernel (r/(4*π^2)) 0‖^2*rootClipMass (oldVariance ellOld r) ν):=by
    dsimp[T]
    rw[hrough]
    linear_combination 4*A0*roughConstant U H β*‖d‖*
      ‖unitHeatKernel (r/(4*π^2)) 0‖^2*rootClipMass (oldVariance ellOld r) ν*htime
  have hh':|∫y,‖HeatMarkov.kernel (r/(4*π^2)) (by positivity) y‖^2*F (y,x) ∂haarAddCircle|≤
      ‖unitHeatKernel (r/(4*π^2)) 0‖^2*(T*sqrt (2/(ell*s))*‖d‖):=by
    convert! hh using 1;ring
  rw[he] at hh'
  have hm:=mul_le_mul_of_nonneg_left hroot
    (show 0≤4*A0*roughConstant U H β*sqrt (2/ell)*s^((β-2)/4)*‖d‖ by positivity [roughConstant_nonneg U H β])
  convert! hh'.trans hm using 1
  ring

end SHE.NativeMeanWordDomination
