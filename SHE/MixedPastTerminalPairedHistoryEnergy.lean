module

public import SHE.CorrelatedTimeLinearEnergy
public import SHE.MixedPastTerminalWordMass
public import SHE.MixedPastTerminalCovarianceHistoryEnergy
public import SHE.MixedPastTerminalEndpointWord
public import SHE.MixedPastTerminalPairedLinearEnergy
public import SHE.HistoryAverageEnergy
public import SHE.MixedPastTerminalPairedTimeEnergy
public import SHE.MixedPastTerminalRMSSections
public import SHE.MixedPastTerminalRMS
public import SHE.MixedPastTerminalPairedAverage
public import SHE.MixedPastTerminalPairedPackets
public import SHE.FiniteFibreAverageEnergy
public import SHE.MixedPastTerminalRootSpatialActual
public import SHE.MixedPastTerminalPairedSpatial
public import SHE.MixedPastTerminalPairedWord
public import SHE.AssignmentGapPartition
public import SHE.MixedPastTerminalRoughSpatialEnergy
public import SHE.MixedPastTerminalRootSpatialEnergy
public import SHE.MixedHilbertInputMoments
public import SHE.MixedPastTerminalSlotSpatial
public import SHE.ControlledTerminalPairedSections
public import SHE.HistoryRelativeEvenMoment
public import SHE.MixedPastTerminalRootHistory
public import SHE.MixedPastTerminalRoughHistory
public import SHE.PairedTerminalConstants
public import SHE.MixedPastTerminalPairedActive
public import SHE.MixedPastTerminalRootEnvelope
public import SHE.HistoryNewestMoment
public import SHE.ControlledTerminalPairedAmplitude
public import SHE.ControlledRelativeScoreForest
public import SHE.TerminalConditionalGeometry
public import SHE.ParentMeanDensity
public import SHE.MixedPastTerminalPairedIdentity
public import SHE.MixedPastTerminalPairedFields
public import SHE.ControlledTerminalPairedRelative
public import SHE.TerminalSuccessorGeometry
public import SHE.MixedPastTerminalState
public import SHE.MixedPastTerminalFirstState
public import SHE.JointHistoryFields
public import SHE.WeightedRowTimeShift
public import SHE.ControlledThetaRelativeArrays
public import SHE.ControlledThetaWeightedFields
public import SHE.MixedPastDecayedWord
public import SHE.RelativeHistoryGeometry
public import SHE.ParentHeatFields
public import SHE.MixedPastActualMean
public import SHE.MixedPastJointData
public import SHE.MixedNativeJointHistory
public import SHE.ControlledJointMeanIdentity
public import SHE.CarrierStopBounds
public import SHE.CoveredControlledLaw
public import SHE.JointWordAnalytic
public import SHE.PastEventWeights
public import SHE.VaryingControlledGaussianFields
public import SHE.MixedNativePastWeightedMoments
public import SHE.MixedNativePastThetaMoments
public import SHE.NativePastHybridMoments
public import SHE.ControlledProfile
public import SHE.PastHybridIntegral
public import SHE.PastItoAlgebra
public import SHE.MixedNativePairObservation
public import SHE.NativePairScaledMartingale
public import SHE.NativePairLocalMartingale
public import SHE.NativePairExtendedMartingale

@[expose] public section
noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000

namespace SHE.MixedPastTerminalPairedHistoryEnergy
open MeasureTheory PredictableL2 NativeHeatObservation NativeObservationNaturality
open FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation StoppedItoInputs
open scoped NNReal ENNReal
local instance mixedPastLiteralPoint_realSigma : MeasurableSpace RealL2 := borel _
local instance mixedPastLiteralPoint_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance mixedPastLiteralPoint_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance mixedPastLiteralPoint_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance mixedPastLiteralPoint_blockSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance mixedPastLiteralPoint_blockBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
variable {Ω : Type} [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
variable (Λ κ : ℝ) (hκ : 0<κ) {aU aV : ℝ→ℝ} (haU : Measurable aU) (haV : Measurable aV) {ell M : ℝ}
variable (hell : 0<ell) (hbU : ∀ z,ell≤aU z ∧ aU z≤M) (hbV : ∀ z,ell≤aV z ∧ aV z≤M)
variable (I₀ I₁ : StandardTerminalIto (C := RealHaarIntegrand.Columns) (E := RealL2) 𝓕 μ H)
variable (u₀ : RealL2)
variable (S : MixedNativeAdditiveResidualPair.Solution 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀)
variable (J : StandardTerminalIto (C := Both RealHaarInput) (E := ℝ) 𝓕 μ H)
variable (hIJ₀ : StandardScalarNaturality I₀ (leftIntegral 𝓕 μ H J))
variable (hIJ₁ : StandardScalarNaturality I₁ (rightIntegral 𝓕 μ H J))

open PastItoInputs PastItoAlgebra PhysicalProfile


local instance mixedPastLiteralPoint_circleSigma : MeasurableSpace CircleL2 := borel _
local instance mixedPastLiteralPoint_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩



open Real AddCircle Set Filter WordRecursion ControlledProfile ControlledReferenceLevel SmoothCylinders UniformSmooth
  CutoffWordLevel CutoffWordHistories CutoffCarriers PhysicalScoreChain PhysicalChainArrays
  PhysicalParentGeometry CoveredHistoryGeometry CoveredControlledLaw ControlledOldIntervals
  ControlledFamilyProfileForest GaussianIncrement GaussianConvolution MeasurableGaussianScores
open scoped BigOperators
local instance mixedPastLiteralPoint_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
variable (P : CanonicalCovariance.ProfileParameters) (haP : BoundedSmooth P.coefficient)
variable (v b : ℝ≥0) (hvb : v ≤ b)
variable (Z : VariableObservations.Family HeatCircle 1)
variable (htarget : ∀ x i,(b:ℝ) ≤ (Z.observations x i).target)
variable (hstop : ∀ x i,(b:ℝ) ≤ (Z.observations x i).stop)
variable (F : HeatCircle→WordRecursion.State 1→ℝ) (hF : UniformBoundedSmooth F)
variable (hFm : Measurable (fun z : HeatCircle×WordRecursion.State 1=>F z.1 z.2))
local notation "Base" => ControlledReferenceThetaGeometry.level P P.coefficient haP Λ v b hvb Z htarget hstop F hF hFm
local notation "Zero" => Base (0,(0,0))
local notation "U" => MixedPastJointData.pastU 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S v
local notation "Dir" => MixedPastJointData.pastD 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S v

local notation "DataU" => MixedNativeJointHistory.firstData 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S
local notation "DataV" => MixedNativeJointHistory.secondData 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S


open MixedPastTerminalPairedFields


local notation "G" => MixedPastTerminalPairedActive.point 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S P haP v b hvb Z htarget hstop F hF hFm
local notation "Raw" => MixedPastTerminalPairedFields.point 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S P haP v b hvb Z htarget hstop F hF hFm
local notation "Amp" => ControlledTerminalPairedAmplitude.amplitude P haP Λ v b hvb Z htarget hstop F hF hFm
local notation "Sc" => ControlledTerminalPairedAmplitude.scale P haP Λ v b hvb Z htarget hstop F hF hFm


open HistoryProductMeasure OrderedHeatForests Classical ProfileL2 ProfileStability
local notation "Src"=>MixedPastTerminalSources.source 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S P haP v b hvb Z htarget hstop F hF hFm
local notation "TimeAmp"=>MixedPastTerminalSlotSpatial.timeAmplitude Λ P haP v b hvb Z htarget hstop F hF hFm





local notation "Spatial"=>MixedPastTerminalPairedAverage.spatial 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP v b hvb Z htarget hstop F hF hFm
local notation "RMS"=>MixedPastTerminalRMS.amplitude (κ:=κ) (M:=M) (Λ:=Λ) (P:=P) (haP:=haP) (v:=v) (b:=b) (hvb:=hvb) (Z:=Z) (htarget:=htarget) (hstop:=hstop) (F:=F) (hF:=hF) (hFm:=hFm)
local notation "En"=>MixedPastTerminalTimeFields.currentEnergy 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP v b hvb Z htarget hstop F hF hFm

local notation "Pair"=>MixedPastTerminalPairedWord.point
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S P haP v b hvb Z htarget hstop F hF hFm
local notation "WordDiff"=>MixedPastTerminalEndpointWord.wordDifference
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S P haP v b hvb Z htarget hstop F hF hFm
local notation "FTC"=>MixedPastTerminalCovarianceHistoryEnergy.ftc
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP v b hvb Z htarget hstop F hF hFm

include hIJ₀ hIJ₁ in
/-- The LITERAL paired finite remainder is absolutely integrable on
sample times ORIGINAL history. Its original-history average has the
sharp paired energy, after genuine space/time/root Fubini and root
probability contraction. No original-history applicability is assumed. -/
theorem actual_history_energy
    (hlocal:StandardTerminalPastLocality J) (hΛ:0≤Λ) (hH:(H:ℝ)≤1) (hvb':v<b)
    (hages:∀x i,(Z.observations x i).stop≤(Z.observations x i).target)
    (hrootstop:∀x i,(Z.observations x i).stop=(b:ℝ))
    (hrootage:∀x i,(Z.observations x i).target=(b:ℝ))
    (hcenter:∀x i,(Z.observations x i).center=x)
    (hspan:(b:ℝ)-(v:ℝ)≤P.horizon) (hbH:b≤H)
    (hsmallP:memoryConstant P.lower P.holder P.exponent*
      ProfileVolterra.powerConstant ((P.exponent-1)/4)*P.horizon^(P.exponent/4)≤1/2)
    (k:ℕ) (hsmall:∀j,j<k+1→(b:ℝ)-(v:ℝ)≤uniformHorizon 1 j)
    {A0 ν χ:ℝ} (hA0:0≤A0) (hν:0≤ν) (hχ:0<χ) (hχβ:χ<P.exponent)
    (hjet:∀x j,j≤k+2→∀z,‖iteratedFDeriv ℝ j (F x) z‖≤A0*ν^j)
    (order:ℕ) (horder:0<order) (ho0:1≤(order:ℝ)*(1-χ))
    (ho1:1≤(order:ℝ)*(1-χ/P.exponent)) (B0 B1 Bcov:ℝ≥0)
    (hBDG:StandardTerminalBDGPower (order*((k+1)+2)) J B0)
    (hBDG1:StandardTerminalBDGPower 1 J B1)
    (hBDGcov:StandardTerminalBDGPower (k+3) J Bcov):
    let η:=Measure.pi (fun _:Fin (k+1)=>volume.restrict (Ioc (v:ℝ) (b:ℝ)))
    let R:=referenceData P P.coefficient haP Λ 0 v b hvb (0,0)
    let W:=fun z:Ω×History HeatCircle (k+1)=>Pair (k+1) ν χ z.2 z.1
    Integrable W (μ.prod (historyMeasure R haarAddCircle (k+1))) ∧
      Integrable (fun ω=>|∫h,W (ω,h) ∂historyMeasure R haarAddCircle (k+1)|^2) μ ∧
      (∫ω,|∫h,W (ω,h) ∂historyMeasure R haarAddCircle (k+1)|^2 ∂μ)≤
        2*(∫t,RMS (k+1) t ν χ A0 order B0 ∂η)*
          ((∫t,RMS (k+1) t ν χ A0 order B0*En (k+1) t^χ ∂η)+
            (∫t,RMS (k+1) t ν χ A0 order B0 ∂η)*
              (∫ω,‖S.second v ω-S.first v ω‖^2 ∂μ)^χ):=by
  intro η R W
  have hcov:=MixedPastTerminalCovarianceHistoryEnergy.actual_history_energy
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S J hIJ₀ hIJ₁
    P haP v b hvb Z htarget hstop F hF hFm hlocal hΛ hsmallP
    (show (v:ℝ)≤1 from (show (v:ℝ)≤(H:ℝ) from by exact_mod_cast hvb.trans hbH).trans hH)
    B1 hBDG1 hages hrootstop hrootage hcenter hvb' hspan hbH k hsmall hA0 hν
    (fun x j hj z=>hjet x j (by omega) z) Bcov hBDGcov
  have hword:=MixedPastTerminalWordMass.word_integrable
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S P haP v b hvb Z htarget hstop F hF hFm
    haarAddCircle (k+1)
  have he:=MixedPastTerminalEndpointWord.word_decomposition_ae
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S P haP v b hvb Z htarget hstop F hF hFm
    hages haarAddCircle (k+1) hA0 hν hχ.le hχβ.le hjet
  have heq:(fun z:Ω×History HeatCircle (k+1)=>WordDiff (k+1) z.2 z.1-FTC k z)=ᵐ[μ.prod (historyMeasure R haarAddCircle (k+1))] W:=by
    filter_upwards [(Measure.quasiMeasurePreserving_snd (μ:=μ)
      (ν:=historyMeasure R haarAddCircle (k+1))).ae he] with z hz
    have hh:=(hz z.1).2
    rw [←MixedPastTerminalCovarianceHistoryEnergy.ftc_eq_interval
      𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP v b hvb Z htarget hstop F hF hFm k z] at hh
    dsimp only [W]
    linarith
  have hi:Integrable W (μ.prod (historyMeasure R haarAddCircle (k+1))):=
    (hword.sub hcov.1).congr heq
  have hm:Measurable W:=(MixedPastTerminalPairedWord.point_measurable
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S P haP v b hvb Z htarget hstop F hF hFm
    (k+1) ν χ).comp measurable_swap
  have ht:=MixedPastTerminalPairedLinearEnergy.actual_linear_energy
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S J hIJ₀ hIJ₁ P haP v b hvb Z htarget hstop F hF hFm
    hlocal hΛ hH hvb' hages (fun x i=>(hrootstop x i).le) hrootage hcenter hspan hbH hsmallP
    k hsmall hA0 hν hχ hχβ hjet order horder ho0 ho1 B0 B1 hBDG hBDG1
  have hRMS:Integrable (fun y:Ω×HeatCircle=>
      |∫t:Fin (k+1)→ℝ,∫w:Fin (k+1)→HeatCircle,
        W (y.1,separated (k+1) (y.2,t,fun j=>w j+y.2))
          ∂Measure.pi (fun _=>haarAddCircle) ∂η|^2) (μ.prod haarAddCircle):=by
    convert! ht.2.1 using 1
  have hh:=HistoryProductMeasure.history_average_energy μ R (k+1) W hm hi hRMS
  refine ⟨hi,hh.1,hh.2.trans ?_⟩
  convert! ht.2.2 using 1

end SHE.MixedPastTerminalPairedHistoryEnergy

