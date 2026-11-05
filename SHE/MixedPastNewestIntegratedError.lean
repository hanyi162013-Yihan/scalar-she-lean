module
public import SHE.MixedPastNewestCurrentEnergy
public import SHE.MixedPastNewestTimeFields
public import SHE.NewestErrorConstants
public import SHE.ScalarApproximationDiscrepancy
public import SHE.PastNewestOldTimeEnergy
public import SHE.MixedPastNewestFields
public import SHE.ParentScoreInput
public import SHE.ParentMeanMass
public import SHE.WeightedSFiniteMoments
public import SHE.PastWordTimeFields

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 2600000
namespace SHE.MixedPastNewestIntegratedError
open Set MeasureTheory ProbabilityTheory Real AddCircle PredictableL2 NativeHeatObservation NativeObservationNaturality
  FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation StoppedItoInputs
  GaussianIncrement ControlledOldIntervals MeasurableGaussianScores PhysicalProfile
  WordRecursion CutoffWordLevel CutoffWordHistories CutoffCarriers PhysicalScoreChain PhysicalChainArrays
  PhysicalParentGeometry ControlledProfile ControlledReferenceLevel ControlledReferenceWindows
  ControlledFamilyProfileForest CoveredHistoryGeometry CoveredControlledLaw SmoothCylinders UniformSmooth GaussianConvolution
open scoped NNReal ENNReal BigOperators
local instance mixedPastNewestIntegratedError_realSigma : MeasurableSpace RealL2:=borel _
local instance mixedPastNewestIntegratedError_realBorel : BorelSpace RealL2:=⟨rfl⟩
local instance mixedPastNewestIntegratedError_rowSigma : MeasurableSpace RealHaarInput:=borel _
local instance mixedPastNewestIntegratedError_rowBorel : BorelSpace RealHaarInput:=⟨rfl⟩
local instance mixedPastNewestIntegratedError_bothSigma : MeasurableSpace (Both RealHaarInput):=borel _
local instance mixedPastNewestIntegratedError_bothBorel : BorelSpace (Both RealHaarInput):=⟨rfl⟩
local instance mixedPastNewestIntegratedError_circleSigma : MeasurableSpace CircleL2:=borel _
local instance mixedPastNewestIntegratedError_circleBorel : BorelSpace CircleL2:=⟨rfl⟩
local instance mixedPastNewestIntegratedError_period : Fact (0<2*π):=⟨by positivity⟩
attribute [local irreducible] MixedPastNewestError.value WordRecursion.directionalSecond
  GaussianConvolution.gaussianAverage UncutSmoothWords.test MeasurableGaussianScores.scoreVariance
  MeasurableGaussianScores.coefficient MeasurableGeneralizedInverse.generalizedInverse
variable {Ω:Type}[MeasurableSpace Ω]
variable (𝓕:Filtration ℝ≥0 ‹MeasurableSpace Ω›)(μ:Measure Ω)[IsProbabilityMeasure μ](H:ℝ≥0)
variable (Λ κ:ℝ)(hκ:0<κ){aU aV:ℝ→ℝ}(haU:Measurable aU)(haV:Measurable aV){ell M:ℝ}
variable (hell:0<ell)(hbU:∀z,ell≤aU z ∧ aU z≤M)(hbV:∀z,ell≤aV z ∧ aV z≤M)
variable (I₀ I₁:StandardTerminalIto (C:=RealHaarIntegrand.Columns) (E:=RealL2) 𝓕 μ H)
variable (u₀:RealL2)
variable (S:MixedNativeAdditiveResidualPair.Solution 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀)
variable (J:StandardTerminalIto (C:=Both RealHaarInput) (E:=ℝ) 𝓕 μ H)
variable (hIJ₀:StandardScalarNaturality I₀ (leftIntegral 𝓕 μ H J))
variable (hIJ₁:StandardScalarNaturality I₁ (rightIntegral 𝓕 μ H J))
variable (P:CanonicalCovariance.ProfileParameters)(haP:BoundedSmooth P.coefficient)
variable (v b:ℝ≥0)(hvb:v≤b)(Z:VariableObservations.Family HeatCircle 1)
variable (htarget:∀x i,(b:ℝ)≤(Z.observations x i).target)
variable (hstop:∀x i,(b:ℝ)≤(Z.observations x i).stop)
variable (F:HeatCircle→WordRecursion.State 1→ℝ)(hF:UniformBoundedSmooth F)
variable (hFm:Measurable (fun z:HeatCircle×WordRecursion.State 1=>F z.1 z.2))
local notation "Base"=>ControlledReferenceThetaGeometry.level P P.coefficient haP Λ v b hvb Z htarget hstop F hF hFm
local notation "Zero"=>Base (0,(0,0))
local notation "Value"=>MixedPastNewestError.value 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S
  P haP v b hvb Z htarget hstop F hF hFm

open HistoryProductMeasure OrderedHeatForests
open ActualMeanKernel
local notation "Active"=>MixedPastNewestFields.active 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S
  P haP v b hvb Z htarget hstop F hF hFm

def integrand (k:ℕ)(θ:ℝ)(e:(ℝ≥0×Ω)×HeatCircle→ℝ)(z:ℝ×(HeatCircle×Ω)):ℝ:=
  MixedPastNewestCurrentEnergy.output 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S
    P haP v b hvb Z htarget hstop F hF hFm k θ z.1.toNNReal
      (fun p=>e ((z.1.toNNReal,p.1),p.2)) z.2

def drift (k:ℕ)(θ:ℝ)(e:(ℝ≥0×Ω)×HeatCircle→ℝ)(z:HeatCircle×Ω):ℝ:=
  ∫q,integrand 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
    P haP v b hvb Z htarget hstop F hF hFm k θ e (q,z) ∂volume.restrict (Ioc (v:ℝ) (b:ℝ))

theorem integrand_measurable (k:ℕ)(θ:ℝ)(e:(ℝ≥0×Ω)×HeatCircle→ℝ)(he:Measurable e):
    Measurable (integrand 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
      P haP v b hvb Z htarget hstop F hF hFm k θ e):=by
  have hm:=MixedPastNewestTimeFields.active_measurable
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP v b hvb Z htarget hstop F hF hFm k e he
  let W:=(ℝ×(HeatCircle×Ω))×(Fin k→ℝ)
  have hQ:Measurable (fun z:W×(Fin k→HeatCircle)=>z.1.1.1.toNNReal):=
    measurable_real_toNNReal.comp measurable_fst.fst.fst
  have hmap:Measurable (fun z:W×(Fin k→HeatCircle)=>
      ((θ,(z.1.1.1.toNNReal,z.1.1.2.2)),separated k (z.1.1.2.1,z.1.2,z.2))):=
    (measurable_const.prodMk (hQ.prodMk measurable_fst.fst.snd.snd)).prodMk
      ((separated_measurable k).comp
        (measurable_fst.fst.snd.fst.prodMk (measurable_fst.snd.prodMk measurable_snd)))
  have hsp:=((hm.comp hmap).stronglyMeasurable.integral_prod_right'
    (ν:=Measure.pi (fun _:Fin k=>haarAddCircle))).measurable
  have hh:=(hsp.stronglyMeasurable.integral_prod_right'
    (ν:=Measure.pi (fun _:Fin k=>volume.restrict (Ioc (v:ℝ) (b:ℝ))))).measurable
  exact hh

def coefficientError (D:SmoothApproximation.ScalarData)(j:ℕ)(p:(ℝ≥0×Ω)×HeatCircle):ℝ:=
  D.residualCoefficient (PredictableScalarField.nativeField (Function.uncurry S.first) p)-
    D.smoothCoefficient j (PredictableScalarField.nativeField (Function.uncurry S.first) p)

theorem coefficientError_measurable (D:SmoothApproximation.ScalarData)(j:ℕ):
    Measurable (coefficientError 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S D j):=by
  have hu:Measurable (Function.uncurry S.first):=(S.first_predictable.mono (predictable_le_product 𝓕)).measurable
  have hm:=PredictableScalarField.nativeField_measurable hu
  exact (D.residual_continuous.measurable.comp hm).sub ((D.smooth_boundedSmooth j).smooth.continuous.measurable.comp hm)

theorem coefficientError_bound (D:SmoothApproximation.ScalarData)(j:ℕ)(p:(ℝ≥0×Ω)×HeatCircle):
    |coefficientError 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S D j p|≤
      ScalarApproximationDiscrepancy.scalarError D j:=ScalarApproximationDiscrepancy.coefficient_error D j _

include hIJ₀ hIJ₁ in
/-- The actual newest ordinary coefficient-error insertion is integrated
in current-time RMS before the final root/sample square. All old and
current collision faces are included. -/
theorem energy {B Hr:ℝ}(hB:0≤B)(hHr:0≤Hr)
    (hroot:∀x z,|F x z|≤B)
    (hrootmod:∀x z w,|F x z-F x w|≤Hr*|z 0-w 0|^P.exponent)
    (hlocal:StandardTerminalPastLocality J)(hΛ:0≤Λ)
    (hages:∀x i,(Z.observations x i).stop≤(Z.observations x i).target)
    (hrootStop:∀x i,(Z.observations x i).stop≤(b:ℝ))
    (hrootTarget:∀x i,(Z.observations x i).target=(b:ℝ))
    (hspan:(b:ℝ)-(v:ℝ)≤P.horizon)(hvb':v<b)(hbH:b≤H)(k:ℕ)
    (hold:∀j,j<k→(b:ℝ)-(v:ℝ)≤uniformHorizon 1 j)
    (A0 ν:ℝ)(hA:0≤A0)(hν:0≤ν)
    (hjet:∀x j,j≤k→∀z,‖iteratedFDeriv ℝ j (F x) z‖≤A0*ν^j)
    (B0:ℝ≥0)(hBDG:StandardTerminalBDGPower (k+2) J B0)
    (ε:ℝ)(hε:0≤ε)(e:(ℝ≥0×Ω)×HeatCircle→ℝ)(he:Measurable e)
    (hecap:∀p,|e p|≤ε)(θ:ℝ)(hθ:|θ|≤1):
    Integrable (integrand 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
      P haP v b hvb Z htarget hstop F hF hFm k θ e)
        ((volume.restrict (Ioc (v:ℝ) (b:ℝ))).prod (haarAddCircle.prod μ)) ∧
    Integrable (fun z:HeatCircle×Ω=>|drift 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
      P haP v b hvb Z htarget hstop F hF hFm k θ e z|^2) (haarAddCircle.prod μ) ∧
    (∫z:HeatCircle×Ω,|drift 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
      P haP v b hvb Z htarget hstop F hF hFm k θ e z|^2 ∂haarAddCircle.prod μ)≤
      ε^2*MixedPastNewestCurrentEnergy.constant κ (M:=M) P v b B Hr k B0 A0 ν*
        (((b:ℝ)-(v:ℝ))^(P.exponent/8)/(P.exponent/8))^2:=by
  let C:=MixedPastNewestCurrentEnergy.constant κ (M:=M) P v b B Hr k B0 A0 ν
  have hC:0≤C:=mul_nonneg
    (mul_nonneg (MixedPastNewestCollision.constant_nonneg κ (M:=M) P hB hHr k B0) (sq_nonneg _))
    (sq_nonneg _)
  let a:=P.exponent/8
  have ha:0<a:=div_pos P.exponent_pos (by norm_num)
  have hvbR:(v:ℝ)<b:=by exact_mod_cast hvb'
  let τ:Measure ℝ:=volume.restrict (Ioc (v:ℝ) (b:ℝ))
  let A:ℝ→ℝ:=fun q=>ε*sqrt C*|((b:ℝ)-q)|^(a-1)
  have hab:Measurable (fun q:ℝ=>|((b:ℝ)-q)|):=
    continuous_abs.measurable.comp (measurable_const.sub measurable_id)
  have hAm:Measurable A:=measurable_const.mul ((real_rpow_measurable _).comp hab)
  have hAn(q:ℝ):0≤A q:=mul_nonneg (mul_nonneg hε (sqrt_nonneg _)) (rpow_nonneg (abs_nonneg _) _)
  have hi0:IntervalIntegrable (fun s:ℝ=>s^(a-1)) volume 0 ((b:ℝ)-v):=
    intervalIntegral.intervalIntegrable_rpow' (by linarith)
  have hi:IntervalIntegrable (fun q:ℝ=>((b:ℝ)-q)^(a-1)) volume v b:=by
    simpa only [sub_self,sub_sub_cancel,sub_zero] using (hi0.comp_sub_left (b:ℝ)).symm
  have hki:Integrable (fun q:ℝ=>((b:ℝ)-q)^(a-1)) τ:=by
    simpa only [τ,uIoc_of_le hvbR.le,IntegrableOn] using hi.def'
  have hAeq:∀ᵐq∂τ,A q=ε*sqrt C*((b:ℝ)-q)^(a-1):=by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with q hq
    dsimp only [A]
    rw [abs_of_nonneg (sub_nonneg.mpr hq.2)]
  have hAi:Integrable A τ:=((hki.const_mul (ε*sqrt C)).congr (hAeq.mono (fun _ h=>h.symm)))
  let G:=integrand 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
    P haP v b hvb Z htarget hstop F hF hFm k θ e
  have hGm:Measurable G:=integrand_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
    P haP v b hvb Z htarget hstop F hF hFm k θ e he
  have hsec:∀ᵐq∂τ,Integrable (fun z:HeatCircle×Ω=>‖G (q,z)‖^2) (haarAddCircle.prod μ) ∧
      (∫z:HeatCircle×Ω,‖G (q,z)‖^2 ∂haarAddCircle.prod μ)≤A q^2:=by
    filter_upwards [ae_restrict_mem measurableSet_Ioc,ae_restrict_of_ae (volume.ae_ne (b:ℝ)),hAeq] with q hq hne hAq
    have hqb:q<(b:ℝ):=lt_of_le_of_ne hq.2 hne
    have hq0:0≤q:=le_trans v.2 hq.1.le
    have hqn:(q.toNNReal:ℝ)=q:=Real.coe_toNNReal q hq0
    have hvqn:v≤q.toNNReal:=by exact_mod_cast (show (v:ℝ)≤(q.toNNReal:ℝ) by simpa only [hqn] using hq.1.le)
    have hqbn:q.toNNReal<b:=by exact_mod_cast (show (q.toNNReal:ℝ)<(b:ℝ) by simpa only [hqn] using hqb)
    have hqH:q.toNNReal≤H:=le_trans hqbn.le hbH
    have hem:Measurable (fun p:Ω×HeatCircle=>e ((q.toNNReal,p.1),p.2)):=
      he.comp ((measurable_const.prodMk measurable_fst).prodMk measurable_snd)
    have hh:=MixedPastNewestCurrentEnergy.energy
      𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S J hIJ₀ hIJ₁ P haP v b hvb Z htarget hstop F hF hFm
      hB hHr hroot hrootmod hlocal hΛ hages hrootStop hrootTarget hspan haarAddCircle k hold 0
      q.toNNReal hvqn hqH hqbn A0 ν hA hν hjet B0 hBDG ε hε _ hem (fun p=>hecap _) θ hθ
    refine ⟨by simpa only [G,integrand,Real.norm_eq_abs] using hh.1,?_⟩
    have hpow:(((b:ℝ)-q)^(a-1))^2=((b:ℝ)-q)^(P.exponent/4-2):=by
      rw [←Real.rpow_mul_natCast (sub_nonneg.mpr hqb.le)]
      congr 1
      dsimp only [a]
      ring
    have hAq2:A q^2=ε^2*C*((b:ℝ)-q)^(P.exponent/4-2):=by
      rw [hAq,mul_pow,mul_pow,sq_sqrt hC,hpow]
    rw [hAq2]
    simpa only [G,integrand,Real.norm_eq_abs,C,hqn] using hh.2
  have hh:=HilbertParameterAverage.finite_energy (haarAddCircle.prod μ) τ G hGm A hAm hAi hAn
    (hsec.mono (fun _ h=>h.1)) (hsec.mono (fun _ h=>h.2))
  have heint:(∫q,((b:ℝ)-q)^(a-1) ∂τ)=((b:ℝ)-(v:ℝ))^a/a:=by
    rw [show τ=volume.restrict (Ioc (v:ℝ) (b:ℝ)) from rfl,
      ←intervalIntegral.integral_of_le hvbR.le,
      intervalIntegral.integral_comp_sub_left (fun s:ℝ=>s^(a-1)) (b:ℝ),sub_self,
      integral_rpow (Or.inl (by linarith:-1<a-1)),show a-1+1=a by ring,
      Real.zero_rpow ha.ne',sub_zero]
  have hmass:(∫q,A q∂τ)=ε*sqrt C*(((b:ℝ)-(v:ℝ))^a/a):=by
    rw [integral_congr_ae hAeq,integral_const_mul,heint]
  refine ⟨hh.1,by simpa only [G,drift,Real.norm_eq_abs] using hh.2.1,?_⟩
  have hb:=hh.2.2
  rw [hmass,mul_pow,mul_pow,sq_sqrt hC] at hb
  simpa only [G,drift,Real.norm_eq_abs,C,a] using hb

end SHE.MixedPastNewestIntegratedError
