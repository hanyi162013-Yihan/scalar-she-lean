module

public import SHE.MixedNativePairedReferenceEnergy
public import SHE.MovingMeanRootScalar
public import SHE.PastReferenceEnergy
public import SHE.MixedNativePairedReferenceHilbert
public import SHE.PastReferenceComparisonSection
public import SHE.PastReferenceMeanTheta
public import SHE.PastReferenceThreeLeg
public import SHE.PastReferenceMeanRealization
public import SHE.PastReferenceCovarianceSection
public import SHE.PastReferenceBaselineSection
public import SHE.NegativeThreeLeg
public import SHE.MixedPastMeanRootL1
public import SHE.MovingRootThreeLeg
public import SHE.MovingMeanRootRealization
public import SHE.MovingCovarianceRootSections
public import SHE.MovingBaselineRootSections
public import SHE.MixedPastMeanThetaFourier
public import SHE.MovingMeanThetaEnergy
public import SHE.MovingMeanSectionEnergy
public import SHE.MeanThetaAverage
public import SHE.MovingMeanCost

@[expose] public section
noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
set_option quotPrecheck false

namespace SHE.MixedNativePairedReferenceOutput
open AddCircle
open MeasureTheory PredictableL2 NativeHeatObservation NativeObservationNaturality
open FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation StoppedItoInputs
open scoped NNReal ENNReal
local instance movingComparisonSection_realSigma : MeasurableSpace RealL2 := borel _
local instance movingComparisonSection_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance movingComparisonSection_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance movingComparisonSection_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance movingComparisonSection_blockSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance movingComparisonSection_blockBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
variable {Ω : Type} [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
variable (Λ κ : ℝ) (hκ : 0<κ) {aU aV : ℝ→ℝ} (haU : Measurable aU) (haV : Measurable aV) {ell M : ℝ}
variable (hell : 0<ell) (hbU : ∀ z,ell≤aU z ∧ aU z≤M) (hbV : ∀ z,ell≤aV z ∧ aV z≤M)
variable (I₀ I₁ : StandardTerminalIto (C := RealHaarIntegrand.Columns) (E := RealL2) 𝓕 μ H)
variable (u₀ : RealL2)
variable (S : MixedNativeAdditiveResidualPair.Solution 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀)

local instance movingComparisonSection_circleSigma : MeasurableSpace CircleL2 := borel _
local instance movingComparisonSection_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩
local instance movingComparisonSection_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
local instance movingComparisonSection_twoFinite : Fact ((2:ℝ≥0∞)≠∞) := ⟨by simp⟩
variable {W : Type} [MeasurableSpace W]



open Set CutoffWordLevel CutoffWordHistories ControlledProfile SmoothCylinders UniformSmooth
  PhysicalScoreChain ControlledOldIntervals
variable (P : CanonicalCovariance.ProfileParameters) (haP : BoundedSmooth P.coefficient)
variable (h : ℝ≥0) (Z : VariableObservations.Family HeatCircle 1)
variable (htarget : ∀ x i,(h:ℝ)≤(Z.observations x i).target)
variable (hstop : ∀ x i,(h:ℝ)≤(Z.observations x i).stop)
variable (F : HeatCircle→WordRecursion.State 1→ℝ) (hF : UniformBoundedSmooth F)
variable (hFm : Measurable (fun z : HeatCircle×WordRecursion.State 1=>F z.1 z.2))
local notation "AA"=>ControlledMeanOldAverageShift.absoluteAt P P.coefficient haP Λ h Z htarget hstop F hF hFm
local notation "ZT" v=>ObservationFamilyTimeShift.family (v:ℝ) Z
local notation "HT" v=>ControlledWordTimeShift.translatedTargets h Z htarget v
local notation "HS" v=>ControlledWordTimeShift.translatedStops h Z hstop v



local notation "Val"=>MovingMeanSectionEnergy.value 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
  P haP h Z htarget hstop F hF hFm

local notation "Avg"=>MovingMeanThetaEnergy.thetaValue 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
  P haP h Z htarget hstop F hF hFm
variable (J : StandardTerminalIto (C:=Both RealHaarInput) (E:=ℝ) 𝓕 μ H)
variable (hIJ₀ : StandardScalarNaturality I₀ (leftIntegral 𝓕 μ H J))
variable (hIJ₁ : StandardScalarNaturality I₁ (rightIntegral 𝓕 μ H J))

local notation "CT"=>MovingMarkRootTheta.covarianceTheta 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S
  P P.coefficient haP h Z htarget hstop F hF hFm
local notation "BT"=>MovingMarkRootTheta.baselineTheta 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S
  P P.coefficient haP h Z htarget hstop F hF hFm

def endpointDifference (k : ℕ) (v s : ℝ≥0) (z : Ω×HeatCircle) : ℝ:=
  MixedNativeRootTransfer.averagedEndpoint 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
    P haP v (v+h) (show v≤v+h from le_self_add) (ZT v) (HT v) (HS v) F hF hFm k 1 (v+s) z-
  MixedNativeRootTransfer.averagedEndpoint 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
    P haP v (v+h) (show v≤v+h from le_self_add) (ZT v) (HT v) (HS v) F hF hFm k 0 (v+s) z

local notation "End"=>endpointDifference 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
  P haP h Z htarget hstop F hF hFm

variable (hnull:NullCompleteFiltration.ContainsNullSets 𝓕 μ)(hJ:StandardFiniteIto.Universal 𝓕 μ H J)
variable (hAs:BoundedSmooth (fun z=>κ+aV z))
variable (hrootStop:∀x i,(Z.observations x i).stop≤(h:ℝ))
variable (hrootTarget:∀x i,(Z.observations x i).target=(h:ℝ))
local notation "RS" v=>(fun x=>by
  change (Z.observations x 0).stop+(v:ℝ)=((v+h:ℝ≥0):ℝ)
  rw [le_antisymm (hrootStop x 0) (hstop x 0),NNReal.coe_add,add_comm])
local notation "RT" v=>(fun x=>by
  change (Z.observations x 0).target+(v:ℝ)=((v+h:ℝ≥0):ℝ)
  rw [hrootTarget x 0,NNReal.coe_add,add_comm])
variable (hL:1≤Λ){ρ:ℝ}(hρ:0≤ρ)
def reference(k:ℕ)(z:ℝ≥0×Ω):CircleL2:=
  MixedNativePairedHilbertExpansion.reference 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
    J hIJ₀ hIJ₁ hnull hJ P hAs z.1 (z.1+h) (show z.1≤z.1+h from le_self_add)
    (ZT z.1) (RS z.1) (RT z.1) F hF hFm hL hρ k z.2
local notation "Ref"=>reference 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
  P h Z hstop F hF hFm J hIJ₀ hIJ₁ hnull hJ hAs hrootStop hrootTarget hL hρ

def realScalar(k:ℕ)(z:ℝ≥0×(Ω×HeatCircle)):ℝ:=
  if z.1+h≤H then
    CT k (z.1,(0,z.2))+
    MovingMeanRootScalar.meanTheta 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
      P haP h Z htarget hstop F hF hFm k (z.1,(0,z.2))+
    BT k (z.1,(0,z.2))
  else 0
local notation "RealScalar"=>realScalar 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
  P haP h Z htarget hstop F hF hFm

theorem realScalar_measurable(hΛ:0≤Λ)
    (hsmall:ProfileStability.memoryConstant P.lower P.holder P.exponent*
      ProfileVolterra.powerConstant ((P.exponent-2)/4)*P.horizon^(P.exponent/4)≤1/2)(k:ℕ):
    Measurable (RealScalar k):=by
  have hg:Measurable (fun z:ℝ≥0×(Ω×HeatCircle)=>(z.1,((0:ℝ≥0),z.2))):=
    measurable_fst.prodMk (measurable_const.prodMk measurable_snd)
  have hc:=(MovingMarkRootTheta.covarianceTheta_measurable
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S P P.coefficient haP h Z htarget hstop F hF hFm hΛ hsmall k).comp hg
  have hb:=(MovingMarkRootTheta.baselineTheta_measurable
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S P P.coefficient haP h Z htarget hstop F hF hFm hΛ hsmall k).comp hg
  have hm:=(MovingMeanRootScalar.meanTheta_measurable
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h Z htarget hstop F hF hFm k).comp hg
  exact ((hc.add hm).add hb).ite
    (measurableSet_le (measurable_fst.add_const h) measurable_const) measurable_const

def output(k:ℕ)(z:ℝ≥0×Ω):CircleL2:=
  NativeBesselFieldAE.value Λ ρ hL hρ
    (fun w:(ℝ≥0×Ω)×HeatCircle=>(RealScalar k (w.1.1,(w.1.2,w.2)):ℂ)) z
local notation "Output"=>output 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
  P haP h Z htarget hstop F hF hFm hL hρ

theorem output_measurable
    (hsmall:ProfileStability.memoryConstant P.lower P.holder P.exponent*
      ProfileVolterra.powerConstant ((P.exponent-2)/4)*P.horizon^(P.exponent/4)≤1/2)(k:ℕ):
    Measurable (Output k):=by
  apply NativeBesselFieldAE.measurable
  exact Complex.continuous_ofReal.measurable.comp
    ((realScalar_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
      P haP h Z htarget hstop F hF hFm (zero_le_one.trans hL) hsmall k).comp
        (measurable_fst.fst.prodMk (measurable_fst.snd.prodMk measurable_snd)))

include hnull hJ hAs hrootStop hrootTarget in
theorem output_eq (hA:P.coefficient=(fun z=>κ+aV z))(hlocal:StandardTerminalPastLocality J)
    (hH:(H:ℝ)≤1)
    (hsmallPoint:ProfileStability.memoryConstant P.lower P.holder P.exponent*
      ProfileVolterra.powerConstant ((P.exponent-2)/4)*P.horizon^(P.exponent/4)≤1/2)
    (hsmallL2:ProfileStability.memoryConstant P.lower P.holder P.exponent*
      ProfileVolterra.powerConstant ((P.exponent-1)/4)*P.horizon^(P.exponent/4)≤1/2)
    (hages:∀x i,(Z.observations x i).stop≤(Z.observations x i).target)
    (hcenter:∀x,(Z.observations x 0).center=x)
    (hspan:(h:ℝ)≤P.horizon)(k:ℕ)
    (hfresh:(h:ℝ)≤UniformFutureProfileScores.horizon (1+k))
    (hold:∀j,j<k→(h:ℝ)≤PhysicalScoreChain.uniformHorizon 1 j)
    (A0 ν:ℝ)(hA0:0≤A0)(hν:0≤ν)
    (hjet:∀x j,j≤k→∀z,‖iteratedFDeriv ℝ j (F x) z‖≤A0*ν^j)
    (Bpast Babs:ℝ≥0)(hBDGpast:StandardTerminalBDGPower 1 J Bpast)
    (hBDGabs:StandardTerminalBDGPower (k+2) J Babs)
    (v:ℝ≥0)(hvH:v+h≤H)(hh:0<h):
    ∀ᵐω∂μ,Output k (v,ω)=Ref k (v,ω):=by
  have ht:=PastReferenceThreeLeg.actual_moving_transfer
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h Z htarget hstop F hF hFm
    J hIJ₀ hIJ₁ hlocal (zero_le_one.trans hL) hH hsmallPoint hsmallL2
    hages hrootStop hrootTarget hcenter hspan k hfresh hold A0 ν hA0 hν hjet
    Bpast hBDGpast Babs hBDGabs v 0 hvH (by rfl) hh
  let Y:Ω×HeatCircle→ℝ:=fun z=>RealScalar k (v,z)
  have hY:Measurable Y:=(realScalar_measurable
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h Z htarget hstop F hF hFm
    (zero_le_one.trans hL) hsmallPoint k).comp (measurable_const.prodMk measurable_id)
  have hfield:∀ᵐz:Ω×HeatCircle∂μ.prod AddCircle.haarAddCircle,
      Y z=MixedNativePairedReferenceAverage.field
        𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP v (v+h)
        (show v≤v+h from le_self_add) (ZT v) (RS v) (RT v) F hF hFm k z:=by
    filter_upwards [ht] with z hz
    rcases z with ⟨ω,x⟩
    simpa only [Y,realScalar,ite_eq_left hvH,MovingMeanRootScalar.meanTheta_eq_absolute,
      MixedNativePairedReferenceAverage.field,add_zero] using hz.symm
  filter_upwards [Measure.ae_ae_of_ae_prod hfield] with ω hω
  have hn:=MixedNativePairedReferenceHilbert.native_eq_of_section
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S J hIJ₀ hIJ₁ hnull hJ P haP hAs
    v (v+h) (show v≤v+h from le_self_add) (ZT v) (RS v) (RT v) F hF hFm
    hsmallPoint (lt_add_of_pos_right v hh) hL hρ hA Y hY k ω hω
  exact hn

end SHE.MixedNativePairedReferenceOutput
