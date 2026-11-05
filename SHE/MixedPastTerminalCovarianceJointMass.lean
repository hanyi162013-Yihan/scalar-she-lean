module

public import SHE.MixedPastTerminalCovarianceThetaEnergy
public import SHE.HistoryAbsoluteTransfer
public import SHE.MixedPastTerminalCovarianceThetaFields
public import SHE.MixedPastTerminalCovarianceAverages
public import SHE.HilbertFiniteAverage
public import SHE.ControlledTerminalCovarianceSections
public import SHE.MixedPastTerminalCovarianceRelativeMass
public import SHE.RandomScoreSpatialAverage
public import SHE.RandomScoreSpatialAbsolute
public import SHE.ParentScoreInput
public import SHE.MixedPastFiniteTerminalMass

public import SHE.MixedPastCovariancePointMoments
public import SHE.MixedPastScoreEnergy
public import SHE.RandomFutureCenters
public import SHE.PastMeanSections
public import SHE.QuarterSpatialEvent
public import SHE.PastCovarianceMassSections

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHE.MixedPastTerminalCovarianceJointMass
open MeasureTheory PredictableL2 NativeHeatObservation NativeObservationNaturality
  FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation StoppedItoInputs
open scoped NNReal ENNReal
local instance mixedPastCovarianceSpatialFields_realSigma : MeasurableSpace RealL2 := borel _
local instance mixedPastCovarianceSpatialFields_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance mixedPastCovarianceSpatialFields_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance mixedPastCovarianceSpatialFields_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance mixedPastCovarianceSpatialFields_blockSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance mixedPastCovarianceSpatialFields_blockBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
variable {Ω : Type} [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
variable (Λ κ : ℝ) (hκ : 0<κ) {aU aV : ℝ→ℝ} (haU : Measurable aU) (haV : Measurable aV) {ell M : ℝ}
variable (hell : 0<ell) (hbU : ∀ z,ell≤aU z ∧ aU z≤M) (hbV : ∀ z,ell≤aV z ∧ aV z≤M)
variable (I₀ I₁ : StandardTerminalIto (C:=RealHaarIntegrand.Columns) (E:=RealL2) 𝓕 μ H)
variable (u₀ : RealL2)
variable (S : MixedNativeAdditiveResidualPair.Solution 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀)
variable (J : StandardTerminalIto (C:=Both RealHaarInput) (E:=ℝ) 𝓕 μ H)
variable (hIJ₀ : StandardScalarNaturality I₀ (leftIntegral 𝓕 μ H J))
variable (hIJ₁ : StandardScalarNaturality I₁ (rightIntegral 𝓕 μ H J))
open Real AddCircle Set Filter WordRecursion ControlledProfile ControlledReferenceLevel SmoothCylinders UniformSmooth
  CutoffWordLevel CutoffWordHistories CutoffCarriers PhysicalScoreChain PhysicalChainArrays
  PhysicalParentGeometry CoveredHistoryGeometry CoveredControlledLaw ControlledOldIntervals
  HistoryProductMeasure ActualMeanKernel
local instance mixedPastCovarianceSpatialFields_circleSigma : MeasurableSpace CircleL2 := borel _
local instance mixedPastCovarianceSpatialFields_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩
local instance mixedPastCovarianceSpatialFields_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
variable (P : CanonicalCovariance.ProfileParameters) (haP : BoundedSmooth P.coefficient)
variable (v b : ℝ≥0) (hvb : v≤b)
variable (Z : VariableObservations.Family HeatCircle 1)
variable (htarget : ∀ x i,(b:ℝ)≤(Z.observations x i).target)
variable (hstop : ∀ x i,(b:ℝ)≤(Z.observations x i).stop)
variable (F : HeatCircle→WordRecursion.State 1→ℝ) (hF : UniformBoundedSmooth F)
variable (hFm : Measurable (fun z : HeatCircle×WordRecursion.State 1=>F z.1 z.2))
local notation "Base" => ControlledReferenceThetaGeometry.level P P.coefficient haP Λ v b hvb Z htarget hstop F hF hFm
local notation "Zero" => Base (0,(0,0))
local notation "U" => MixedPastJointData.pastU 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S v
local notation "Dir" => MixedPastJointData.pastD 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S v
local notation "Mean" => MixedPastLiteralPoint.meanField 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S P haP v b hvb Z htarget hstop F hF hFm

open ScalarRootRelativeGeometry ControlledResidualScoreInput MeasurableGaussianScores
  ProfileStability QuarterSpatialEvent OrderedHeatForests
local notation "Actual" => MixedPastLiteralCovariance.actualPoint 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S P haP v b hvb Z htarget hstop F hF hFm

local notation "G"=>MixedPastTerminalCovarianceFields.active 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S P haP v b hvb Z htarget hstop F hF hFm
local notation "MActual"=>MixedPastTerminalCovarianceFields.mass 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S P haP v b hvb Z htarget hstop F hF hFm

local notation "Point"=>MixedPastTerminalCovarianceSpatialFields.relativePoint
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP v b hvb Z htarget hstop F hF hFm
local notation "Mass"=>MixedPastFiniteTerminalMass.scoreMass
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP v b hvb Z htarget hstop F hF hFm
local notation "TA"=>ControlledTerminalCovarianceSections.timeAmplitude
  P haP Λ v b hvb Z htarget hstop F hF hFm

local notation "Avg"=>MixedPastTerminalCovarianceAverages.oldSpaceAverage
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP v b hvb Z htarget hstop F hF hFm
local notation "AA"=>TerminalCovarianceTimeIntegral.activeAmplitude
  P haP Λ v b hvb Z htarget hstop F hF hFm

local notation "TimeAvg"=>MixedPastTerminalCovarianceThetaFields.timeAverage
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP v b hvb Z htarget hstop F hF hFm
local notation "ThetaAvg"=>MixedPastTerminalCovarianceThetaFields.thetaAverage
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP v b hvb Z htarget hstop F hF hFm

def integrand (k:ℕ) (z:ℝ×(Ω×History HeatCircle (k+1))):ℝ:=
  G (k+1) z.1 z.2.2 z.2.1
local notation "Field"=>integrand 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
  P haP v b hvb Z htarget hstop F hF hFm

theorem integrand_measurable (k:ℕ):Measurable (Field k):=by
  classical
  have hp:Measurable (fun z:ℝ×(Ω×History HeatCircle (k+1))=>
      MixedPastTerminalFiniteCovariance.point
        𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S P haP v b hvb Z htarget hstop F hF hFm
        (k+1) 1 0 1 z.1 z.2.2 z.2.1):=
    MixedPastTerminalFiniteCovariance.point_variable_measurable
      𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S P haP v b hvb Z htarget hstop F hF hFm
      (k+1) _ measurable_snd.snd _ measurable_snd.fst
      (fun _=>1) (fun _=>0) (fun _=>1) Prod.fst
      measurable_const measurable_const measurable_const measurable_fst
  exact hp.ite ((strictHistory_measurableSet Zero (k+1)).preimage measurable_snd.snd) measurable_const

include hIJ₀ hIJ₁ in
/-- TRUE absolute original-history covariance mass, before any signed
history or interpolation average, with the exact finite time budget. -/
theorem actual_history_mass
    (hlocal:StandardTerminalPastLocality J) (hΛ:0≤Λ)
    (hsmallL2:memoryConstant P.lower P.holder P.exponent*
      ProfileVolterra.powerConstant ((P.exponent-1)/4)*P.horizon^(P.exponent/4)≤1/2)
    (hv1:(v:ℝ)≤1) (Bpast:ℝ≥0) (hBDGpast:StandardTerminalBDGPower 1 J Bpast)
    (hages:∀x i,(Z.observations x i).stop≤(Z.observations x i).target)
    (hrootstop:∀x i,(Z.observations x i).stop=(b:ℝ))
    (hrootage:∀x i,(Z.observations x i).target=(b:ℝ))
    (hcenter:∀x i,(Z.observations x i).center=x)
    (hvb':v<b) (hspan:(b:ℝ)-(v:ℝ)≤P.horizon) (hbH:b≤H) (k:ℕ)
    (hsmall:∀j,j<k+1→(b:ℝ)-(v:ℝ)≤uniformHorizon 1 j)
    {ζ:ℝ} (hζ:0≤ζ) (hζ1:ζ≤1)
    {A0 ν:ℝ} (hA0:0≤A0) (hν:0≤ν)
    (hjet:∀x j,j≤k+1→∀z,‖iteratedFDeriv ℝ j (F x) z‖≤A0*ν^j)
    (B0:ℝ≥0) (hBDG:StandardTerminalBDGPower (k+3) J B0):
    let CC:=MixedPastWordMoments.momentConstant P (k+1) (k+1) 1
      (((k+1:ℕ):ℝ)*(NativeHybridMoments.momentConstant (k+3) B0 κ M)^P.exponent)
    let Cm:=2*P.holder*(3*(((1+k:ℕ):ℝ)/(P.lower/2)))
    let EE:=(∫ω,‖S.second v ω-S.first v ω‖^2 ∂μ)^P.exponent
    let B:=QuarterRMSTimeFactors.oldTimeBudget P (fraction P*P.lower) (uniformConstant 1)
      (k+1) ((b:ℝ)-(v:ℝ)) 0 1 A0 ν
    let R:=referenceData P P.coefficient haP Λ 0 v b hvb (0,0)
    Integrable (fun z:Ω×History HeatCircle (k+1)=>Field k (ζ,z))
      (μ.prod (historyMeasure R haarAddCircle (k+1))) ∧
      (∫z,|Field k (ζ,z)| ∂μ.prod (historyMeasure R haarAddCircle (k+1)))≤
        (Real.sqrt (CC*Cm^2*EE)*(Fintype.card (Choices 1 (k+1)):ℝ))*(B/2):=by
  intro CC Cm EE B R
  let C:=Real.sqrt (CC*Cm^2*EE)*(Fintype.card (Choices 1 (k+1)):ℝ)
  let A:=fun t:Fin (k+1)→ℝ=>C*AA (k+1) A0 ν t
  have hC:0≤C:=mul_nonneg (Real.sqrt_nonneg _) (Nat.cast_nonneg _)
  have hA0'(t):0≤A t:=mul_nonneg hC (TerminalCovarianceTimeIntegral.activeAmplitude_nonneg
    P haP Λ v b hvb Z htarget hstop F hF hFm (k+1) A0 ν t)
  have ht:=TerminalCovarianceTimeIntegral.old_time_integral
    P haP Λ v b hvb Z htarget hstop F hF hFm hvb' (k+1) hA0 hν
  have hAi:Integrable A (Measure.pi (fun _:Fin (k+1)=>volume.restrict (Ioc (v:ℝ) (b:ℝ)))):=ht.1.const_mul _
  have hF0:Measurable (fun z:Ω×History HeatCircle (k+1)=>Field k (ζ,z)):=
    (integrand_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
      P haP v b hvb Z htarget hstop F hF hFm k).comp (measurable_const.prodMk measurable_id)
  have hs0:=MixedPastTerminalCovarianceSpatialEnergy.actual_spatial_energy_ae
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S J hIJ₀ hIJ₁
    P haP v b hvb Z htarget hstop F hF hFm hlocal hΛ hsmallL2 hv1 Bpast hBDGpast
    hages hrootstop hrootage hcenter hspan hbH k hsmall hζ hζ1 hA0 hν hjet B0 hBDG
  have hs:∀ᵐt ∂Measure.pi (fun _:Fin (k+1)=>volume.restrict (Ioc (v:ℝ) (b:ℝ))),
      let GG:=fun z:(Ω×HeatCircle)×(Fin (k+1)→HeatCircle)=>
        Field k (ζ,(z.1.1,separated (k+1) (z.1.2,t,fun i=>z.2 i+z.1.2)))
      Integrable GG ((μ.prod haarAddCircle).prod (Measure.pi (fun _:Fin (k+1)=>haarAddCircle))) ∧
      (∫z,|GG z| ∂(μ.prod haarAddCircle).prod (Measure.pi (fun _:Fin (k+1)=>haarAddCircle)))≤A t:=by
    filter_upwards [hs0] with t hts
    intro GG
    by_cases hp:StrictHistory Zero (k+1) (anchor (k+1) t)
    · have hh:=hts hp
      have hnode:(carrier Zero (k+1)).terminal (anchor (k+1) t)=(anchor (k+1) t).2.1:=
        ClippedCovariance.clip_eq ⟨hp.2.1.le,hp.2.2.le⟩
      have ha:StrictHistory Zero (k+1) (anchor (k+1) t) ∧
          (v:ℝ)<(carrier Zero (k+1)).terminal (anchor (k+1) t):=⟨hp,by rw [hnode];exact hp.2.1⟩
      have he:AA (k+1) A0 ν t=TA (k+1) t A0 ν:=ite_eq_left ha
      refine ⟨hh.1,hh.2.2.2.trans_eq ?_⟩
      dsimp only [A,C]
      rw [he]
      ring
    · have hz(z:(Ω×HeatCircle)×(Fin (k+1)→HeatCircle)):GG z=0:=by
        have hn:¬StrictHistory Zero (k+1) (separated (k+1) (z.1.2,t,fun i=>z.2 i+z.1.2)):=by
          intro hh
          exact hp ((FixedHistoryTimeFactors.strict_sections Zero (b:ℝ) (fun _=>rfl)
            (k+1) t z.1.2 0 _ (fun _=>0)).mp hh)
        exact ite_eq_right hn
      refine ⟨?_,?_⟩
      · exact (integrable_zero _ _ _ : Integrable (fun _:(Ω×HeatCircle)×(Fin (k+1)→HeatCircle)=>(0:ℝ))
          ((μ.prod haarAddCircle).prod (Measure.pi (fun _:Fin (k+1)=>haarAddCircle)))).congr
          (ae_of_all _ (fun z=>(hz z).symm))
      · simpa only [hz,abs_zero,integral_zero] using hA0' t
  have ho:=HistoryProductMeasure.original_absolute R μ (k+1)
    (fun z=>Field k (ζ,z)) hF0 A hAi hs
  refine ⟨ho.1,ho.2.trans ?_⟩
  change (∫t,C*AA (k+1) A0 ν t ∂Measure.pi (fun _:Fin (k+1)=>volume.restrict (Ioc (v:ℝ) (b:ℝ))))≤_
  rw [integral_const_mul]
  exact mul_le_mul_of_nonneg_left ht.2 hC

include hIJ₀ hIJ₁ in
/-- Genuine joint interpolation/original sample/history absolute
integrability. This discharges the covariance FTC's remaining Fubini
premise rather than interchanging conditionally convergent averages. -/
theorem actual_joint_mass
    (hlocal:StandardTerminalPastLocality J) (hΛ:0≤Λ)
    (hsmallL2:memoryConstant P.lower P.holder P.exponent*
      ProfileVolterra.powerConstant ((P.exponent-1)/4)*P.horizon^(P.exponent/4)≤1/2)
    (hv1:(v:ℝ)≤1) (Bpast:ℝ≥0) (hBDGpast:StandardTerminalBDGPower 1 J Bpast)
    (hages:∀x i,(Z.observations x i).stop≤(Z.observations x i).target)
    (hrootstop:∀x i,(Z.observations x i).stop=(b:ℝ))
    (hrootage:∀x i,(Z.observations x i).target=(b:ℝ))
    (hcenter:∀x i,(Z.observations x i).center=x)
    (hvb':v<b) (hspan:(b:ℝ)-(v:ℝ)≤P.horizon) (hbH:b≤H) (k:ℕ)
    (hsmall:∀j,j<k+1→(b:ℝ)-(v:ℝ)≤uniformHorizon 1 j)
    {A0 ν:ℝ} (hA0:0≤A0) (hν:0≤ν)
    (hjet:∀x j,j≤k+1→∀z,‖iteratedFDeriv ℝ j (F x) z‖≤A0*ν^j)
    (B0:ℝ≥0) (hBDG:StandardTerminalBDGPower (k+3) J B0):
    Integrable (Field k) (MeanThetaAverage.thetaMeasure.prod
      (μ.prod (historyMeasure (referenceData P P.coefficient haP Λ 0 v b hvb (0,0)) haarAddCircle (k+1)))):=by
  let R:=referenceData P P.coefficient haP Λ 0 v b hvb (0,0)
  let CC:=MixedPastWordMoments.momentConstant P (k+1) (k+1) 1
    (((k+1:ℕ):ℝ)*(NativeHybridMoments.momentConstant (k+3) B0 κ M)^P.exponent)
  let Cm:=2*P.holder*(3*(((1+k:ℕ):ℝ)/(P.lower/2)))
  let EE:=(∫ω,‖S.second v ω-S.first v ω‖^2 ∂μ)^P.exponent
  let B:=QuarterRMSTimeFactors.oldTimeBudget P (fraction P*P.lower) (uniformConstant 1)
    (k+1) ((b:ℝ)-(v:ℝ)) 0 1 A0 ν
  let D:=(Real.sqrt (CC*Cm^2*EE)*(Fintype.card (Choices 1 (k+1)):ℝ))*(B/2)
  let F0:=fun z:(Ω×History HeatCircle (k+1))×ℝ=>Field k (z.2,z.1)
  have hF0:Measurable F0:=(integrand_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
    P haP v b hvb Z htarget hstop F hF hFm k).comp measurable_swap
  have hs:∀ᵐζ ∂MeanThetaAverage.thetaMeasure,
      Integrable (fun z=>F0 (z,ζ)) (μ.prod (historyMeasure R haarAddCircle (k+1))) ∧
      (∫z,|F0 (z,ζ)| ∂μ.prod (historyMeasure R haarAddCircle (k+1)))≤D:=by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with ζ hζ
    exact actual_history_mass 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S J hIJ₀ hIJ₁
      P haP v b hvb Z htarget hstop F hF hFm hlocal hΛ hsmallL2 hv1 Bpast hBDGpast
      hages hrootstop hrootage hcenter hvb' hspan hbH k hsmall hζ.1.le hζ.2 hA0 hν hjet B0 hBDG
  have hh:=SectionFirstMoment.joint_integrable (μ.prod (historyMeasure R haarAddCircle (k+1)))
    MeanThetaAverage.thetaMeasure F0 hF0 (fun _=>D) (integrable_const _) hs
  convert! hh.1.swap using 1

end SHE.MixedPastTerminalCovarianceJointMass
