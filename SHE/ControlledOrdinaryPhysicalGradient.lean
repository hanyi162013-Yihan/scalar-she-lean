module
public import SHE.ControlledReferenceFamilyBackward
public import SHE.OrdinaryUncutPhysicalGradient
public import SHE.ParameterSmoothContinuity

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
namespace SHE.ControlledOrdinaryPhysicalGradient
open Set MeasureTheory StoppedFourier WordRecursion ControlledProfile ControlledReferenceLevel
  CutoffWordLevel CutoffWordHistories SmoothCylinders UniformSmooth PredictableL2 FiniteHaar DyadicApproximation OrthogonalItoChannels
open scoped NNReal ENNReal
local instance controlledOrdinaryPhysicalGradient_period:Fact (0<2*Real.pi):=⟨by positivity⟩
local instance controlledOrdinaryPhysicalGradient_nativeSigma:MeasurableSpace CircleL2:=borel _
local instance controlledOrdinaryPhysicalGradient_nativeBorel:BorelSpace CircleL2:=⟨rfl⟩
local instance controlledOrdinaryPhysicalGradient_rowSigma:MeasurableSpace RealHaarInput:=borel _
local instance controlledOrdinaryPhysicalGradient_rowBorel:BorelSpace RealHaarInput:=⟨rfl⟩
local instance controlledOrdinaryPhysicalGradient_blockSigma:MeasurableSpace (Both RealHaarInput):=borel _
local instance controlledOrdinaryPhysicalGradient_blockBorel:BorelSpace (Both RealHaarInput):=⟨rfl⟩
variable (P:CanonicalCovariance.ProfileParameters)(A:ℝ→ℝ)(hA:BoundedSmooth A)
variable (Λ θ:ℝ)(v b:ℝ≥0)(hvb:v≤b)
variable {Y:Type}[MeasurableSpace Y]{n:ℕ}(Z:VariableObservations.Family Y n)
variable (htarget:∀y i,(b:ℝ)≤(Z.observations y i).target)(hstop:∀y i,(b:ℝ)≤(Z.observations y i).stop)
variable (F:Y→WordRecursion.State n→ℝ)(hF:UniformBoundedSmooth F)
variable (hFm:Measurable (fun q:Y×WordRecursion.State n=>F q.1 q.2))
local notation "Base"=>ControlledReferenceFamilyLevel.level P A hA Λ θ v b hvb Z htarget hstop F hF hFm
local notation "NL"=>(fun p k=>UncutWordEvaluation.normalizedLevel (Base p) k)
variable (hsmall:ProfileStability.memoryConstant P.lower P.holder P.exponent*
  ProfileVolterra.powerConstant ((P.exponent-2)/4)*P.horizon^(P.exponent/4)≤1/2)

include hsmall in
theorem normalized_gradient_continuous(hΛ:0≤Λ)(k:ℕ)(h:History Y k)(t:ℝ):
    Continuous (fun q:Inputs×WordRecursion.State (n+k)=>
      fderiv ℝ (GaussianItoTest.backward ((NL q.1 k).window h) ((NL q.1 k).test h) t) q.2):=by
  have hFs:=CutoffWordLevel.uniform_reindex
    (ControlledReferenceFamilyBounds.normalized_uniform P A hA Λ θ v b hvb Z htarget hstop F hF hFm k)
    (fun p:Inputs=>(p,h))
  have hFn:=ControlledReferenceFamilyContinuity.normalized_continuous P A hA Λ θ v b hvb Z htarget hstop F hF hFm hsmall hΛ k h
  have hC:=ControlledReferenceFamilyBackward.window_path_continuous P A hA Λ θ v b hvb Z htarget hstop F hF hFm hsmall hΛ k h t
  obtain ⟨C,_,hCb⟩:=hFs.norm_bound
  have hc:=GaussianParameterContinuity.continuous_average (fun p:Inputs=>(NL p k).test h) hFn hCb
    (fun p:Inputs=>((NL p k).window h).path t) hC
  have hs:=hFs.average (fun p:Inputs=>ProbabilityTheory.multivariateGaussian 0 (((NL p k).window h).path t).val) (fun _=>inferInstance)
  obtain ⟨B,hB,hBb⟩:=hs.fderiv.fderiv.norm_bound
  exact ParameterSmoothContinuity.continuous_fderiv _ hc (fun p=>(hs.smooth p).of_le (by simp)) hB hBb

variable {Ω:Type}[MeasurableSpace Ω]
variable {𝓕:Filtration ℝ≥0 ‹MeasurableSpace Ω›}{μ:Measure Ω}[IsProbabilityMeasure μ]
variable {H:ℝ≥0}{κ:ℝ}{a:ℝ→ℝ}{ell M:ℝ}(m:TwoChannelCutoffModel.Model 𝓕 μ H κ a ell M)
include hsmall in
/-- Past-reference substitution changes only the actual Gaussian word,
while ordinary U and both of its physical Haar rows remain fixed. -/
theorem raw_parameter_continuous(hΛ:0≤Λ)(k:ℕ)(z:History Y k×(ℝ≥0×Ω)):
    Continuous (fun p:Inputs=>OrdinaryUncutPhysicalGradient.raw m (Base p) k z):=by
  have ho(p:Inputs):(NL p k).observations.observations z.1=(NL (0,0) k).observations.observations z.1:=
    ControlledReferenceFamilyBounds.carrier_observations_eq P A hA Λ θ v b hvb Z htarget hstop F hF hFm p (0,0) k z.1
  have ht(p:Inputs):(NL p k).terminal z.1=(NL (0,0) k).terminal z.1:=
    ControlledReferenceFamilyBounds.carrier_terminal_eq P A hA Λ θ v b hvb Z htarget hstop F hF hFm p (0,0) k z.1
  have hw(p:Inputs):UncutSmoothWords.weight (Base p) k z.1=UncutSmoothWords.weight (Base (0,0)) k z.1:=
    ControlledReferenceFamilyBounds.weight_eq P A hA Λ θ v b hvb Z htarget hstop F hF hFm p (0,0) k z.1
  let y:=OrdinaryPhysicalGradient.mean m (NL (0,0) k) z
  have hy(p:Inputs):OrdinaryPhysicalGradient.mean m (NL p k) z=y:=by
    unfold OrdinaryPhysicalGradient.mean
    rw [ho]
    rfl
  have hbase(p:Inputs):(referenceData P A hA Λ θ v b hvb p).base=(v:ℝ):=rfl
  by_cases hz:(v:ℝ)<(z.2.1:ℝ)∧(z.2.1:ℝ)<(NL (0,0) k).terminal z.1
  · have hg:=(normalized_gradient_continuous P A hA Λ θ v b hvb Z htarget hstop F hF hFm hsmall hΛ k z.1 (z.2.1:ℝ)).comp
      (continuous_id.prodMk (continuous_const (y:=y)))
    have hs:=continuous_finsetSum Finset.univ (fun i:Fin (n+k)=>fun _=>
      (hg.clm_apply (continuous_const (y:=EuclideanSpace.basisFun (Fin (n+k)) ℝ i))).smul
        (continuous_const (y:=OrdinaryPhysicalGradient.row m ((NL (0,0) k).observations.observations z.1) z.2 i)))
    convert! hs.const_smul (UncutSmoothWords.weight (Base (0,0)) k z.1) using 1
    funext p
    simp only [OrdinaryUncutPhysicalGradient.raw,OrdinaryPhysicalGradient.raw,ht,ho,hw,hy,hbase]
    rw [if_pos hz]
    rfl
  · have he:(fun p:Inputs=>OrdinaryUncutPhysicalGradient.raw m (Base p) k z)=fun _=>0:=by
      funext p
      simp only [OrdinaryUncutPhysicalGradient.raw,OrdinaryPhysicalGradient.raw,ht,hbase,if_neg hz,smul_zero]
    rw [he]
    exact continuous_const

end SHE.ControlledOrdinaryPhysicalGradient
