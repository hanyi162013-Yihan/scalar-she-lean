module
public import SHE.MixedPastNewestSpatial
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
namespace SHE.MixedPastNewestAverage
open Set MeasureTheory ProbabilityTheory Real AddCircle PredictableL2 NativeHeatObservation NativeObservationNaturality
  FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation StoppedItoInputs
  GaussianIncrement ControlledOldIntervals MeasurableGaussianScores PhysicalProfile
  WordRecursion CutoffWordLevel CutoffWordHistories CutoffCarriers PhysicalScoreChain PhysicalChainArrays
  PhysicalParentGeometry ControlledProfile ControlledReferenceLevel ControlledReferenceWindows
  ControlledFamilyProfileForest CoveredHistoryGeometry CoveredControlledLaw SmoothCylinders UniformSmooth GaussianConvolution
open scoped NNReal ENNReal BigOperators
local instance mixedPastNewestAverage_realSigma : MeasurableSpace RealL2:=borel _
local instance mixedPastNewestAverage_realBorel : BorelSpace RealL2:=⟨rfl⟩
local instance mixedPastNewestAverage_rowSigma : MeasurableSpace RealHaarInput:=borel _
local instance mixedPastNewestAverage_rowBorel : BorelSpace RealHaarInput:=⟨rfl⟩
local instance mixedPastNewestAverage_bothSigma : MeasurableSpace (Both RealHaarInput):=borel _
local instance mixedPastNewestAverage_bothBorel : BorelSpace (Both RealHaarInput):=⟨rfl⟩
local instance mixedPastNewestAverage_circleSigma : MeasurableSpace CircleL2:=borel _
local instance mixedPastNewestAverage_circleBorel : BorelSpace CircleL2:=⟨rfl⟩
local instance mixedPastNewestAverage_period : Fact (0<2*π):=⟨by positivity⟩
attribute [local irreducible] MixedPastNewestError.value WordRecursion.directionalSecond
  GaussianConvolution.gaussianAverage UncutSmoothWords.test MeasurableGaussianScores.scoreVariance
  MeasurableGaussianScores.coefficient MeasurableGeneralizedInverse.generalizedInverse
variable {Ω:Type}[MeasurableSpace Ω]{X:Type}[MeasurableSpace X]
variable (𝓕:Filtration ℝ≥0 ‹MeasurableSpace Ω›)(μ:Measure Ω)[IsProbabilityMeasure μ](H:ℝ≥0)
variable (Λ κ:ℝ)(hκ:0<κ){aU aV:ℝ→ℝ}(haU:Measurable aU)(haV:Measurable aV){ell M:ℝ}
variable (hell:0<ell)(hbU:∀z,ell≤aU z ∧ aU z≤M)(hbV:∀z,ell≤aV z ∧ aV z≤M)
variable (I₀ I₁:StandardTerminalIto (C:=RealHaarIntegrand.Columns) (E:=RealL2) 𝓕 μ H)
variable (u₀ v₀:RealL2)
variable (S:MixedNativeAdditiveResidualPair.Solution 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀)
variable (J:StandardTerminalIto (C:=Both RealHaarInput) (E:=ℝ) 𝓕 μ H)
variable (hIJ₀:StandardScalarNaturality I₀ (leftIntegral 𝓕 μ H J))
variable (hIJ₁:StandardScalarNaturality I₁ (rightIntegral 𝓕 μ H J))
variable (P:CanonicalCovariance.ProfileParameters)(haP:BoundedSmooth P.coefficient)
variable (v b:ℝ≥0)(hvb:v≤b)(Z:VariableObservations.Family X 1)
variable (htarget:∀x i,(b:ℝ)≤(Z.observations x i).target)
variable (hstop:∀x i,(b:ℝ)≤(Z.observations x i).stop)
variable (F:X→WordRecursion.State 1→ℝ)(hF:UniformBoundedSmooth F)
variable (hFm:Measurable (fun z:X×WordRecursion.State 1=>F z.1 z.2))
local notation "Base"=>ControlledReferenceThetaGeometry.level P P.coefficient haP Λ v b hvb Z htarget hstop F hF hFm
local notation "Zero"=>Base (0,(0,0))
local notation "Value"=>MixedPastNewestError.value 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
  P haP v b hvb Z htarget hstop F hF hFm

open HistoryProductMeasure OrderedHeatForests
open ActualMeanKernel
local notation "Active"=>MixedPastNewestFields.active 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
  P haP v b hvb Z htarget hstop F hF hFm

def spatial (k:ℕ)(θ:ℝ)(q:ℝ≥0)(e:Ω×HeatCircle→ℝ)(x:X)(z:(Fin k→ℝ)×Ω):ℝ:=
  ∫w:Fin k→HeatCircle,Active k θ q e (z.2,separated k (x,z.1,w))
    ∂Measure.pi (fun _=>haarAddCircle)

theorem spatial_measurable (k:ℕ)(θ:ℝ)(q:ℝ≥0)(e:Ω×HeatCircle→ℝ)(he:Measurable e)(x:X):
    Measurable (spatial 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
      P haP v b hvb Z htarget hstop F hF hFm k θ q e x):=by
  have hm:=MixedPastNewestFields.active_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
    P haP v b hvb Z htarget hstop F hF hFm k θ q e he
  have hmap:Measurable (fun z:((Fin k→ℝ)×Ω)×(Fin k→HeatCircle)=>
      (z.1.2,separated k (x,z.1.1,z.2))):=measurable_fst.snd.prodMk
    ((separated_measurable k).comp (measurable_const.prodMk (measurable_fst.fst.prodMk measurable_snd)))
  have hh:=((hm.comp hmap).stronglyMeasurable.integral_prod_right'
    (ν:=Measure.pi (fun _:Fin k=>haarAddCircle))).measurable
  exact hh

theorem active_zero_of_not_strict (k:ℕ)(θ:ℝ)(q:ℝ≥0)(e:Ω×HeatCircle→ℝ)
    (h:History X k)(hn:¬StrictHistory Zero k h)(ω:Ω):Active k θ q e (ω,h)=0:=by
  let a:ℝ×Inputs:=(θ,(MixedPastJointData.pastU
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S v ω,
      MixedPastJointData.pastD 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S v ω))
  have hn':¬StrictHistory (Base a) k h:=fun hs=>hn
    ((ControlledThetaPhysicalGeometry.strict_iff P P.coefficient haP Λ v b hvb Z htarget hstop F hF hFm
      a (0,(0,0)) k h).mp hs)
  have hz:gaussianAverage (WordRecursion.covariance
      (referenceData P P.coefficient haP Λ a.1 v b hvb a.2).reference
      ((carrier (Base a) k).observations.observations h) q ((carrier (Base a) k).terminal h))
        (UncutSmoothWords.test (Base a) k h)=fun _:WordRecursion.State (1+k)=>(0:ℝ):=by
    funext z
    simp only [test_zero_of_not_strict _ _ _ hn',gaussianAverage,Pi.zero_apply,integral_zero]
  unfold MixedPastNewestFields.active
  split_ifs
  · unfold MixedPastNewestError.value
    change (1/2:ℝ)*∫y:HeatCircle,e (ω,y)*WordRecursion.directionalSecond
      (gaussianAverage (WordRecursion.covariance
        (referenceData P P.coefficient haP Λ a.1 v b hvb a.2).reference
        ((carrier (Base a) k).observations.observations h) q ((carrier (Base a) k).terminal h))
          (UncutSmoothWords.test (Base a) k h)) _ _ ∂haarAddCircle=0
    rw [hz]
    have hd:fderiv ℝ (fun _:WordRecursion.State (1+k)=>(0:ℝ))=
        fun _=>0:=funext (fun z=>(hasFDerivAt_const (0:ℝ) z).fderiv)
    have hdd(z:WordRecursion.State (1+k)):fderiv ℝ (fderiv ℝ (fun _:WordRecursion.State (1+k)=>(0:ℝ))) z=0:=by
      rw [hd]
      exact (hasFDerivAt_const (0:WordRecursion.State (1+k)→L[ℝ]ℝ) z).fderiv
    simp only [WordRecursion.directionalSecond,WordRecursion.hessian,hdd,
      ContinuousLinearMap.zero_apply,mul_zero,integral_zero]
  · rfl

include hIJ₀ hIJ₁ in
/-- Actual old space and old time are both averaged before the sample
square. The finite constant is chosen before theta, the random error,
and its uniform size, and is independent of smooth-companion derivatives. -/
theorem energy_ae {B Hr:ℝ}(hB:0≤B)(hHr:0≤Hr)
    (hroot:∀x z,|F x z|≤B)
    (hrootmod:∀x z w,|F x z-F x w|≤Hr*|z 0-w 0|^P.exponent)
    (hlocal:StandardTerminalPastLocality J)(hΛ:0≤Λ)
    (hages:∀x i,(Z.observations x i).stop≤(Z.observations x i).target)
    (hrootStop:∀x i,(Z.observations x i).stop≤(b:ℝ))
    (hrootTarget:∀x i,(Z.observations x i).target=(b:ℝ))
    (hspan:(b:ℝ)-(v:ℝ)≤P.horizon)(ρ:Measure X)[IsFiniteMeasure ρ](k:ℕ)
    (hold:∀j,j<k→(b:ℝ)-(v:ℝ)≤uniformHorizon 1 j)
    (x0:X)(q:ℝ≥0)(hvq:v≤q)(hqH:q≤H)(hqb:q<b)
    (A0 ν:ℝ)(hA:0≤A0)(hν:0≤ν)
    (hjet:∀x j,j≤k→∀z,‖iteratedFDeriv ℝ j (F x) z‖≤A0*ν^j)
    (B0:ℝ≥0)(hBDG:StandardTerminalBDGPower (k+2) J B0):
    ∃K:ℝ,0≤K ∧
      K=(∫t,PastNewestTimeIntegral.activeTotal Zero P (fraction P*P.lower) (uniformConstant 1)
        k q (P.exponent/8) A0 ν (separated k (x0,t,fun _=>0))
          ∂Measure.pi (fun _:Fin k=>volume.restrict (Ioc (v:ℝ) (b:ℝ)))) ∧
      ∀ε:ℝ,0≤ε→∀e:Ω×HeatCircle→ℝ,Measurable e→(∀p,|e p|≤ε)→
      ∀θ:ℝ,|θ|≤1→∀ᵐx∂ρ,
        let old:=Measure.pi (fun _:Fin k=>volume.restrict (Ioc (v:ℝ) (b:ℝ)))
        let raw:=spatial 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
          P haP v b hvb Z htarget hstop F hF hFm k θ q e x
        Integrable raw (old.prod μ) ∧ Integrable (fun ω=>|∫t,raw (t,ω) ∂old|^2) μ ∧
          (∫ω,|∫t,raw (t,ω) ∂old|^2 ∂μ)≤ε^2*MixedPastNewestCollision.constant κ (M:=M) P B Hr k B0*
            (Fintype.card (Choices 1 k):ℝ)^2*K^2:=by
  let ellOld:=fraction P*P.lower
  have hellOld:0<ellOld:=mul_pos (fraction_pos P) P.lower_pos
  have hCs(j):0≤uniformConstant 1 j:=(uniformConstant_pos 1 j).le
  have hT:∀x,(Zero).terminal x=(b:ℝ):=fun _=>rfl
  obtain ⟨K,hK,hKmass,havg⟩:=PastNewestTimeIntegral.old_time_energy Zero μ P (b:ℝ) hT hellOld
    (uniformConstant 1) hCs k x0 (fun _=>0) (by exact_mod_cast hvq) (by exact_mod_cast hqb)
      le_rfl hA hν
  refine ⟨K,hK,hKmass,?_⟩
  intro ε hε e he hecap θ hθ
  have hsp:=MixedPastNewestSpatial.energy_ae
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S J hIJ₀ hIJ₁ P haP v b hvb Z htarget hstop F hF hFm
      hB hHr hroot hrootmod hlocal hΛ hages hrootStop hspan ρ k
  filter_upwards [hsp] with x hx
  dsimp only
  let old:=Measure.pi (fun _:Fin k=>volume.restrict (Ioc (v:ℝ) (b:ℝ)))
  let raw:=spatial 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
    P haP v b hvb Z htarget hstop F hF hFm k θ q e x
  have hraw:Measurable raw:=spatial_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
    P haP v b hvb Z htarget hstop F hF hFm k θ q e he x
  let D:=MixedPastNewestCollision.constant κ (M:=M) P B Hr k B0*(Fintype.card (Choices 1 k):ℝ)^2
  have hD:0≤D:=mul_nonneg (MixedPastNewestCollision.constant_nonneg κ (M:=M) P hB hHr k B0) (sq_nonneg _)
  have hsame(t:Fin k→ℝ):
      (StrictHistory Zero k (separated k (x,t,fun _=>0)) ∧ (q:ℝ)<(carrier Zero k).terminal (separated k (x,t,fun _=>0)))↔
      (StrictHistory Zero k (separated k (x0,t,fun _=>0)) ∧ (q:ℝ)<(carrier Zero k).terminal (separated k (x0,t,fun _=>0))):=by
    rw [FixedHistoryTimeFactors.strict_sections Zero (b:ℝ) hT k t x x0 (fun _=>0) (fun _=>0),
      terminal_separated Zero (b:ℝ) hT,terminal_separated Zero (b:ℝ) hT]
  have hs:∀ᵐt∂old,StrictHistory Zero k (separated k (x0,t,fun _=>0)) ∧
      (q:ℝ)<(carrier Zero k).terminal (separated k (x0,t,fun _=>0))→
      Integrable (fun ω=>|raw (t,ω)|^2) μ ∧
      (∫ω,|raw (t,ω)|^2 ∂μ)≤ε^2*D*timeWeight Zero ellOld (uniformConstant 1) k (separated k (x0,t,fun _=>0))^2*
        PastWordTimeFields.total Zero P k (separated k (x0,t,fun _=>0)) A0 ν*
          ((carrier Zero k).terminal (separated k (x0,t,fun _=>0))-q)^(P.exponent/4-2):=by
    filter_upwards [hx] with t ht
    intro ha
    have ha':=(hsame t).mpr ha
    have hsmall:SmallHistory Zero (uniformHorizon 1) k (separated k (x,t,fun _=>0)):=
      RelativeHistoryGeometry.smallHistory_of_span Zero (b:ℝ) (fun _=>le_rfl)
        (fun a i=>(hrootTarget a i).le) (uniformHorizon 1) k hold _
    have hh:=ht q hvq hqH ha'.2 ha'.1 hsmall θ hθ A0 ν hA hν (hjet x) B0 hBDG ε hε e he hecap
    have hW:=FixedHistoryTimeFactors.timeWeight_sections Zero (b:ℝ) hT ellOld (uniformConstant 1) k t x x0 (fun _=>0) (fun _=>0)
    have hl:=FixedHistoryTimeFactors.lower_sections Zero (b:ℝ) hT k t x x0 (fun _=>0) (fun _=>0)
    have hu:=FixedHistoryTimeFactors.upper_sections Zero (b:ℝ) hT k t x x0 (fun _=>0) (fun _=>0)
    have htar:=FixedHistoryTimeFactors.targets_sections Zero (b:ℝ) hT (fun _:Fin 1=>(b:ℝ)) hrootTarget
      k t x x0 (fun _=>0) (fun _=>0)
    have htotal:PastWordTimeFields.total Zero P k (separated k (x,t,fun _=>0)) A0 ν=
      PastWordTimeFields.total Zero P k (separated k (x0,t,fun _=>0)) A0 ν:=by
      unfold PastWordTimeFields.total
      rw [hl,hu,htar]
    have hrawEq(ω:Ω):(∫w:Fin k→HeatCircle,Active k θ q e (ω,replaceSpace k (separated k (x,t,fun _=>0)) w)
      ∂Measure.pi (fun _=>haarAddCircle))=raw (t,ω):=by
        simp only [raw,spatial,replaceSpace_separated]
    dsimp only at hh
    simp_rw [hrawEq] at hh
    refine ⟨hh.1,?_⟩
    have hb:=hh.2
    rw [hW,htotal] at hb
    have hterm:(carrier Zero k).terminal (separated k (x,t,fun _=>0))=
        (carrier Zero k).terminal (separated k (x0,t,fun _=>0)):=
      (terminal_separated Zero (b:ℝ) hT k t x _).trans (terminal_separated Zero (b:ℝ) hT k t x0 _).symm
    have hpow:=congrArg (fun s:ℝ=>(s-q)^(P.exponent/4-2)) hterm
    refine hb.trans_eq ?_
    rw [hpow]
    dsimp only [D,ellOld]
    ring
  have hz(t:Fin k→ℝ)(hn:¬(StrictHistory Zero k (separated k (x0,t,fun _=>0)) ∧
      (q:ℝ)<(carrier Zero k).terminal (separated k (x0,t,fun _=>0))))(ω:Ω):raw (t,ω)=0:=by
    apply integral_eq_zero_of_ae
    filter_upwards [] with w
    by_cases hp:StrictHistory Zero k (separated k (x,t,fun _=>0))
    · have hq':¬(q:ℝ)<(carrier Zero k).terminal (separated k (x,t,fun _=>0)):=fun hq'=>hn ((hsame t).mp ⟨hp,hq'⟩)
      simp only [MixedPastNewestFields.active,terminal_separated Zero (b:ℝ) hT] at hq' ⊢
      exact ite_eq_right hq'
    · have hn':¬StrictHistory Zero k (separated k (x,t,w)):=by
        simpa only [←replaceSpace_separated k x t (fun _=>0) w,replaceSpace_strict_iff] using hp
      exact active_zero_of_not_strict 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
        P haP v b hvb Z htarget hstop F hF hFm k θ q e _ hn' ω
  have hh:=havg ε D hε hD raw hraw hs hz
  change Integrable raw (old.prod μ) ∧ Integrable (fun ω=>|∫t,raw (t,ω) ∂old|^2) μ ∧
    (∫ω,|∫t,raw (t,ω) ∂old|^2 ∂μ)≤ε^2*D*K^2 at hh
  change Integrable raw (old.prod μ) ∧ Integrable (fun ω=>|∫t,raw (t,ω) ∂old|^2) μ ∧
    (∫ω,|∫t,raw (t,ω) ∂old|^2 ∂μ)≤_
  exact ⟨hh.1,hh.2.1,hh.2.2.trans_eq (by dsimp only [D];ring)⟩

end SHE.MixedPastNewestAverage
