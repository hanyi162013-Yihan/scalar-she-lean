module
public import SHE.MixedPastNewestError
public import SHE.FreshMassInterpolation

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 2400000
namespace SHE.MixedPastNewestInterpolation
open Set MeasureTheory ProbabilityTheory Real AddCircle PredictableL2 NativeHeatObservation NativeObservationNaturality
  FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation StoppedItoInputs
  GaussianIncrement ControlledOldIntervals MeasurableGaussianScores PhysicalProfile
  WordRecursion CutoffWordLevel CutoffWordHistories CutoffCarriers PhysicalScoreChain PhysicalChainArrays
  PhysicalParentGeometry ControlledProfile ControlledReferenceLevel ControlledReferenceWindows
  ControlledFamilyProfileForest CoveredHistoryGeometry CoveredControlledLaw SmoothCylinders UniformSmooth GaussianConvolution
open scoped NNReal ENNReal BigOperators
local instance mixedPastNewestInterpolation_realSigma : MeasurableSpace RealL2:=borel _
local instance mixedPastNewestInterpolation_realBorel : BorelSpace RealL2:=⟨rfl⟩
local instance mixedPastNewestInterpolation_rowSigma : MeasurableSpace RealHaarInput:=borel _
local instance mixedPastNewestInterpolation_rowBorel : BorelSpace RealHaarInput:=⟨rfl⟩
local instance mixedPastNewestInterpolation_bothSigma : MeasurableSpace (Both RealHaarInput):=borel _
local instance mixedPastNewestInterpolation_bothBorel : BorelSpace (Both RealHaarInput):=⟨rfl⟩
local instance mixedPastNewestInterpolation_circleSigma : MeasurableSpace CircleL2:=borel _
local instance mixedPastNewestInterpolation_circleBorel : BorelSpace CircleL2:=⟨rfl⟩
local instance mixedPastNewestInterpolation_period : Fact (0<2*π):=⟨by positivity⟩
attribute [local irreducible] MixedPastNewestError.value WordRecursion.directionalSecond
  GaussianConvolution.gaussianAverage UncutSmoothWords.test MeasurableGaussianScores.scoreVariance
  MeasurableGaussianScores.coefficient MeasurableGeneralizedInverse.generalizedInverse
variable {Ω:Type*}[MeasurableSpace Ω]{X:Type}[MeasurableSpace X]
variable (𝓕:Filtration ℝ≥0 ‹MeasurableSpace Ω›)(μ:Measure Ω)[IsProbabilityMeasure μ](H:ℝ≥0)
variable (Λ κ:ℝ)(hκ:0<κ){aU aV:ℝ→ℝ}(haU:Measurable aU)(haV:Measurable aV){ell M:ℝ}
variable (hell:0<ell)(hbU:∀z,ell≤aU z ∧ aU z≤M)(hbV:∀z,ell≤aV z ∧ aV z≤M)
variable (I₀ I₁:StandardTerminalIto (C:=RealHaarIntegrand.Columns) (E:=RealL2) 𝓕 μ H)
variable (u₀ v₀:RealL2)
variable (S:MixedNativeAdditiveResidualPair.Solution 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀)
variable (P:CanonicalCovariance.ProfileParameters)(haP:BoundedSmooth P.coefficient)
variable (v b:ℝ≥0)(hvb:v≤b)(Z:VariableObservations.Family X 1)
variable (htarget:∀x i,(b:ℝ)≤(Z.observations x i).target)
variable (hstop:∀x i,(b:ℝ)≤(Z.observations x i).stop)
variable (F:X→WordRecursion.State 1→ℝ)(hF:UniformBoundedSmooth F)
variable (hFm:Measurable (fun z:X×WordRecursion.State 1=>F z.1 z.2))
local notation "Base"=>ControlledReferenceThetaGeometry.level P P.coefficient haP Λ v b hvb Z htarget hstop F hF hFm
local notation "Zero"=>Base (0,(0,0))
local notation "U"=>MixedPastJointData.pastU 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S v
local notation "Dir"=>MixedPastJointData.pastD 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S v
local notation "Mean"=>MixedPastLiteralPoint.meanField 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
  P haP v b hvb Z htarget hstop F hF hFm
local notation "Value"=>MixedPastNewestError.value 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
  P haP v b hvb Z htarget hstop F hF hFm

def holderCost (B Hr:ℝ)(k:ℕ):ℝ:=
  (1+B+(P.upper+P.upper)/2)^(k+1)*GaussianAudit.secondScoreAbsIncrementMoment P.exponent*
    (Hr+(k:ℝ)*P.holder/2)*IntervalScoreHolderMass.constant (1+k) P.lower P.exponent

theorem holderCost_nonneg {B Hr:ℝ}(hB:0≤B)(hHr:0≤Hr)(k:ℕ):0≤holderCost P B Hr k:=by
  have hm:0≤GaussianAudit.secondScoreAbsIncrementMoment P.exponent:=integral_nonneg (fun _=>by positivity)
  have hu:=P.upper_nonneg
  have hh:=P.holder_nonneg
  have hl:=P.lower_pos
  have hc:=StoppedFourier.heatConstant_pos
  unfold holderCost IntervalScoreHolderMass.constant
  positivity

/-- Uniform-in-current-mean fresh collision cap for the LITERAL newest
error insertion, on one random-past-compatible physical history event. -/
theorem bad_bound_ae {B Hr:ℝ}(hB:0≤B)(hHr:0≤Hr)
    (hroot:∀x z,|F x z|≤B)
    (hrootmod:∀x z w,|F x z-F x w|≤Hr*|z 0-w 0|^P.exponent)
    (hages:∀x i,(Z.observations x i).stop≤(Z.observations x i).target)
    (hspan:(b:ℝ)-(v:ℝ)≤P.horizon)(ρ:Measure X)[IsFiniteMeasure ρ](k:ℕ):
    ∀ᵐh∂historyMeasure (referenceData P P.coefficient haP Λ 0 v b hvb (0,0)) ρ k,
      ∀q:ℝ≥0,v≤q→(q:ℝ)<(carrier Zero k).terminal h→
      ∀hp:StrictHistory Zero k h,SmallHistory Zero (uniformHorizon 1) k h→
      ∀θ ε:ℝ,0≤ε→∀e:Ω×HeatCircle→ℝ,Measurable e→(∀p,|e p|≤ε)→∀ω:Ω,
      let oldEnvelope:=timeWeight Zero (fraction P*P.lower) (uniformConstant 1) k h*
        OrderedHeatForests.parentDensity 2 (by norm_num) k (targets Zero k h)
          (carrier_orderedTimes Zero hages k h hp) (centers Zero k h)
      |Value k θ q h e ω|≤(ε/2)*((2:ℝ)^k*oldEnvelope)*holderCost P B Hr k*
        ((carrier Zero k).terminal h-q)^(P.exponent/4-1) := by
  let ellOld:=fraction P*P.lower
  have hellOld:0<ellOld:=mul_pos (fraction_pos P) P.lower_pos
  have hc(a:Inputs):Measurable (oldProfile P Λ v a):=
    (coefficient_section_measurable P Λ 0 v a).const_mul (fraction P)
  have hcb(a:Inputs)(p:StoppedGaussianFeatures.Domain):ellOld≤oldProfile P Λ v a p ∧
      oldProfile P Λ v a p≤P.lower/2:=referenceProfile_bounds P Λ a.1 a.2 (p.1-v,p.2)
  have hfloor(p:StoppedGaussianFeatures.Domain):ellOld≤
      (referenceData P P.coefficient haP Λ 0 v b hvb (0,0)).reference p:=by
    have he:=referenceProfile_bounds P Λ (0:CircleL2) 0 (0,0)
    exact ((he.1.trans he.2).trans (half_le_self P.lower_pos.le)).trans
      (coefficient_bounds P Λ 0 v (0,0) p).1
  filter_upwards [ControlledFreshHolderMass.all_parameters_ae P haP Λ v b hvb Z htarget hstop F hF hFm
      hB hHr hroot hrootmod hages ρ k,
    uniform_all_profiles_forest_ae Zero hellOld hfloor (oldProfile P Λ v) hc hcb hages ρ k]
    with h hholder hforest
  intro q hvq hqt hp hsmall θ ε hε e he hecap ω
  dsimp only
  let a:ℝ×Inputs:=(θ,(U ω,Dir ω))
  let Hx:=fun y:HeatCircle=>WordRecursion.directionalSecond
    (gaussianAverage (WordRecursion.covariance
      (referenceData P P.coefficient haP Λ a.1 v b hvb a.2).reference
      ((carrier (Base a) k).observations.observations h) q ((carrier (Base a) k).terminal h))
        (UncutSmoothWords.test (Base a) k h)) (Mean k θ q ω h)
          (heatRow ((carrier (Base a) k).observations.observations h) q y)
  have hterm:=ControlledReferenceThetaGeometry.carrier_terminal_eq P P.coefficient haP Λ v b hvb
    Z htarget hstop F hF hFm a (0,(0,0)) k h
  have hq':(q:ℝ)<(carrier (Base a) k).terminal h:=by rwa [hterm]
  have hδ:(carrier (Base a) k).terminal h-q≤1:=by
    rw [hterm]
    have ht: (carrier Zero k).terminal h≤(b:ℝ):=terminal_le_initial Zero k h
    have hqv:(v:ℝ)≤(q:ℝ):=by exact_mod_cast hvq
    linarith [P.horizon_le_one]
  obtain ⟨hHi,hHb⟩:=hholder a q q.2 hq' hδ (Mean k θ q ω h)
  change Integrable Hx haarAddCircle at hHi
  have hobs:=ControlledReferenceThetaGeometry.carrier_observations_eq P P.coefficient haP Λ v b hvb
    Z htarget hstop F hF hFm a (0,(0,0)) k h
  have hprod:=ControlledThetaPhysicalGeometry.scoreProduct_eq P P.coefficient haP Λ v b hvb
    Z htarget hstop F hF hFm a (0,(0,0)) ((carrier Zero k).observations.observations h)
      (oldProfile P Λ v a.2) k h
  have hHold:(∫y,|Hx y| ∂haarAddCircle)≤((2:ℝ)^k*
      (timeWeight Zero ellOld (uniformConstant 1) k h*
        OrderedHeatForests.parentDensity 2 (by norm_num) k (targets Zero k h)
          (carrier_orderedTimes Zero hages k h hp) (centers Zero k h)))*holderCost P B Hr k*
            ((carrier Zero k).terminal h-q)^(P.exponent/4-1):=by
    change (∫y,|Hx y| ∂haarAddCircle)≤_ at hHb
    rw [hobs,hprod,hterm] at hHb
    have hh:=(hforest (U ω,Dir ω)).2 hp hsmall
    change scoreProduct Zero ((carrier Zero k).observations.observations h)
      (oldProfile P Λ v (U ω,Dir ω)) k h ≤
      timeWeight Zero ellOld (uniformConstant 1) k h*
        OrderedHeatForests.parentDensity 2 (by norm_num) k (targets Zero k h)
          (carrier_orderedTimes Zero hages k h hp) (centers Zero k h) at hh
    have hK:0≤holderCost P B Hr k*((carrier Zero k).terminal h-q)^(P.exponent/4-1):=
      mul_nonneg (holderCost_nonneg P hB hHr k) (Real.rpow_nonneg (sub_pos.mpr hqt).le _)
    have ht:=mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hh (pow_nonneg (by norm_num:(0:ℝ)≤2) k)) hK
    exact hHb.trans (ht.trans_eq (by ring))
  have hmult(y:HeatCircle):‖e (ω,y)*Hx y‖≤ε*|Hx y|:=by
    rw [norm_mul,Real.norm_eq_abs,Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (hecap (ω,y)) (abs_nonneg _)
  have hGi:Integrable (fun y:HeatCircle=>e (ω,y)*Hx y) haarAddCircle:=
    (hHi.abs.const_mul ε).mono' (((he.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable).mul
      hHi.aestronglyMeasurable) (ae_of_all _ hmult)
  have hcap:|Value k θ q h e ω|≤(ε/2)*(∫y,|Hx y| ∂haarAddCircle):=by
    unfold MixedPastNewestError.value
    change |(1/2:ℝ)*∫y,e (ω,y)*Hx y ∂haarAddCircle|≤_
    rw [abs_mul,abs_of_pos (by norm_num:(0:ℝ)<1/2)]
    have hh:=norm_integral_le_of_norm_le (hHi.abs.const_mul ε) (ae_of_all _ hmult)
    simp only [Real.norm_eq_abs,integral_const_mul] at hh
    exact (mul_le_mul_of_nonneg_left hh (by norm_num:(0:ℝ)≤1/2)).trans_eq (by ring)
  exact hcap.trans ((mul_le_mul_of_nonneg_left hHold (div_nonneg hε (by norm_num))).trans_eq (by ring))

end SHE.MixedPastNewestInterpolation
