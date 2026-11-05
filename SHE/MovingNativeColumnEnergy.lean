module
public import SHE.MovingNativeAverageTranslation
public import SHE.MovingNativeColumnTranslation
public import SHE.MovingNativeColumnAverages
public import SHE.MixedPastNativeCompleteColumns
public import SHE.ShiftedOldTimeMeasure
public import SHE.MovingNativeColumns
public import SHE.MixedPastNativeOldTimeEnergy
public import SHE.MixedPastSignedEndpointFields
public import SHE.NativeKernelCongruence
public import SHE.ShiftedPhysicalArrays
public import SHE.NativeRowTimeShift
public import SHE.MovingNativeSpatialKernel
public import SHE.ControlledMeanSpatialShift
public import SHE.MixedPastNativeKernelSemigroup

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
set_option quotPrecheck false
namespace SHE.MovingNativeColumnEnergy
open MeasureTheory PredictableL2 NativeHeatObservation NativeObservationNaturality
open FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation StoppedItoInputs
open scoped NNReal ENNReal
local instance movingNativePointTranslation_realSigma : MeasurableSpace RealL2 := borel _
local instance movingNativePointTranslation_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance movingNativePointTranslation_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance movingNativePointTranslation_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance movingNativePointTranslation_blockSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance movingNativePointTranslation_blockBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
local instance : MeasurableSpace CircleHeat.CircleL2:=borel _
local instance : BorelSpace CircleHeat.CircleL2:=⟨rfl⟩
variable {Ω : Type} [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
variable (Λ κ : ℝ) (hκ : 0<κ) {aU aV : ℝ→ℝ} (haU : Measurable aU) (haV : Measurable aV) {ell M : ℝ}
variable (hell : 0<ell) (hbU : ∀ z,ell≤aU z ∧ aU z≤M) (hbV : ∀ z,ell≤aV z ∧ aV z≤M)
variable (I₀ I₁ : StandardTerminalIto (C := RealHaarIntegrand.Columns) (E := RealL2) 𝓕 μ H)
variable (u₀ : RealL2)
variable (S : MixedNativeAdditiveResidualPair.Solution 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀)
open PastItoInputs PastItoAlgebra PhysicalProfile


local instance movingNativePointTranslation_circleSigma : MeasurableSpace CircleL2 := borel _
local instance movingNativePointTranslation_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩



open Real AddCircle Set Filter WordRecursion ControlledProfile ControlledReferenceLevel SmoothCylinders UniformSmooth
  CutoffWordLevel CutoffWordHistories CutoffCarriers PhysicalScoreChain PhysicalChainArrays
  PhysicalParentGeometry CoveredHistoryGeometry CoveredControlledLaw ControlledOldIntervals
  ControlledFamilyProfileForest GaussianIncrement GaussianConvolution MeasurableGaussianScores
open ProfileStability ProfileL2
open HistoryProductMeasure
open scoped BigOperators
local instance movingNativePointTranslation_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
local instance movingNativePointTranslation_nativeSecond:SecondCountableTopology CircleL2:=
  (_root_.fourierBasis (T:=2*Real.pi)).repr.toHomeomorph.secondCountableTopology
variable (P:CanonicalCovariance.ProfileParameters)(haP:BoundedSmooth P.coefficient)
variable (h:ℝ≥0)(Z:VariableObservations.Family HeatCircle 1)
variable (htarget:∀x i,(h:ℝ)≤(Z.observations x i).target)
variable (hstop:∀x i,(h:ℝ)≤(Z.observations x i).stop)
variable (F:HeatCircle→WordRecursion.State 1→ℝ)(hF:UniformBoundedSmooth F)
variable (hFm:Measurable (fun z:HeatCircle×WordRecursion.State 1=>F z.1 z.2))
local notation "Base"=>ControlledWordTimeShift.relativeLevel P P.coefficient haP Λ h Z htarget hstop F hF hFm
local notation "Zero"=>Base (0,(0,0))
local notation "Past" v:max ω:max=>(embed (S.first v ω),embed (S.second v ω-S.first v ω))

local notation "Abs"=>ControlledWordTimeShift.absoluteLevel P P.coefficient haP Λ h Z htarget hstop F hF hFm
local notation "ZT" v:max=>ObservationFamilyTimeShift.family (v:ℝ) Z
local notation "HT" v:max=>ControlledWordTimeShift.translatedTargets h Z htarget v
local notation "HS" v:max=>ControlledWordTimeShift.translatedStops h Z hstop v
local notation "Mean"=>MovingNativeKernelFields.mean 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h Z htarget hstop F hF hFm

local notation "LeftA" v:max=>MixedPastNativeCompleteColumns.left 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP
  v (v+h) le_self_add (ZT v) (HT v) (HS v) F hF hFm
local notation "RightA" v:max=>MixedPastNativeCompleteColumns.right 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP
  v (v+h) le_self_add (ZT v) (HT v) (HS v) F hF hFm
local notation "Left"=>MovingNativeColumnAverages.left 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h Z htarget hstop F hF hFm
local notation "Right"=>MovingNativeColumnAverages.right 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h Z htarget hstop F hF hFm

variable (J:StandardTerminalIto (C:=Both RealHaarInput) (E:=ℝ) 𝓕 μ H)
variable (hIJ₀:StandardScalarNaturality I₀ (leftIntegral 𝓕 μ H J))
variable (hIJ₁:StandardScalarNaturality I₁ (rightIntegral 𝓕 μ H J))

include hIJ₀ hIJ₁ in
/-- Actual complete-window Borel columns obey the sharp common/signed
energy cap. Every old-time translation occurs before the norm square. -/
theorem energy(k:ℕ)(hΛ:0<Λ)(hlocal:StandardTerminalPastLocality J)
    (hsmallPoint:ProfileStability.memoryConstant P.lower P.holder P.exponent*
      ProfileVolterra.powerConstant ((P.exponent-2)/4)*P.horizon^(P.exponent/4)≤1/2)
    (hsmallL2:ProfileStability.memoryConstant P.lower P.holder P.exponent*
      ProfileVolterra.powerConstant ((P.exponent-1)/4)*P.horizon^(P.exponent/4)≤1/2)
    (hrootTarget:∀x i,(Z.observations x i).target=(h:ℝ))
    (hrootStop:∀x i,(Z.observations x i).stop=(h:ℝ))(hcenter:∀x i,(Z.observations x i).center=x)
    (hspan:(h:ℝ)≤P.horizon)
    (hspanF:(h:ℝ)≤NativeUniversalConstants.rowHorizon (1+k))
    (hspanC:(h:ℝ)≤4*Real.pi^2*NativeUniversalConstants.currentHorizon.{0} (1+k) (by omega))
    (hspanS:(h:ℝ)≤UniformFutureProfileScores.horizon (1+k))
    (hHistory:∀j,j<k→(h:ℝ)≤uniformHorizon 1 j)
    (v s:ℝ≥0)(hs:0<s)(hsh:s<h)(hvhH:v+h≤H)(hH:(H:ℝ)≤1)
    (B1:ℝ≥0)(hBDG1:StandardTerminalBDGPower 1 J B1)
    (A0 ν:ℝ)(hA0:0≤A0)(hν:0≤ν)
    (hjet:∀x j,j≤k→∀z,‖iteratedFDeriv ℝ j (F x) z‖≤A0*ν^j)
    (p:ℕ)(hp:0<p)(Bcur:ℝ≥0)(hBDGcur:StandardTerminalBDGPower (p*(k+2)) J Bcur)
    (Bword:ℝ≥0)(hBDGword:StandardTerminalBDGPower (k+2) J Bword)
    (χ:ℝ)(hχ:0≤χ)(hχ1:χ<1)(horder:1≤(p:ℝ)*(1-χ))
    (mass ρ lam ε tail η:ℝ)(hmass:1≤mass)(hρ:0<ρ)(hρhalf:ρ<1/2)
    (hlam:1≤lam)(htail:tail≤ε*(2*((p-1:ℕ):ℝ)))(hη:0<η)(hρη:ρ+η<1):
    Integrable (fun ω=>‖Left hΛ.le k hmass hρ.le ((v,s),ω)‖^2) μ ∧
      Integrable (fun ω=>‖Right hΛ.le k hmass hρ.le ((v,s),ω)‖^2) μ ∧
      (∫ω,‖Left hΛ.le k hmass hρ.le ((v,s),ω)‖^2 ∂μ)+
        (∫ω,‖Right hΛ.le k hmass hρ.le ((v,s),ω)‖^2 ∂μ)≤
        4*(MixedPastNativeCompleteColumns.commonBudget
          𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P v (v+h) k (v+s) A0 ν ρ χ p Bcur Bword)^2+
        2*(MixedPastNativeCompleteColumns.signedBudget
          𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P v (v+h)
          k (v+s) A0 ν mass ρ lam ε tail η hmass hρ hρhalf p Bcur)^2:=by
  have htarget':∀x i,((ZT v).observations x i).target=((v+h):ℝ):=by
    intro x i
    change (Z.observations x i).target+(v:ℝ)=((v+h):ℝ)
    rw [hrootTarget]
    exact add_comm _ _
  have hstop':∀x i,((ZT v).observations x i).stop=((v+h):ℝ):=by
    intro x i
    change (Z.observations x i).stop+(v:ℝ)=((v+h):ℝ)
    rw [hrootStop]
    exact add_comm _ _
  have hcenter':∀x i,((ZT v).observations x i).center=x:=hcenter
  have hqH:v+s≤H:=(add_le_add le_rfl hsh.le).trans hvhH
  have hq1:((v+s):ℝ)≤1:=le_trans (by exact_mod_cast hqH) hH
  have hwidth1:((v+h):ℝ)-((v+s):ℝ)≤1:=by
    have hr:((v+h):ℝ)≤1:=le_trans (by exact_mod_cast hvhH) hH
    linarith [show (0:ℝ)≤(v+s:ℝ≥0) from (v+s).2]
  have he:=MixedPastNativeCompleteColumns.energy
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S J hIJ₀ hIJ₁
    P haP v (v+h) le_self_add (ZT v) (HT v) (HS v) F hF hFm
    k hΛ hlocal hsmallPoint hsmallL2 htarget' hstop' hcenter'
    (by simpa only [NNReal.coe_add,add_sub_cancel_left] using hspan)
    (by simpa only [NNReal.coe_add,add_sub_cancel_left] using hspanF)
    (by simpa only [NNReal.coe_add,add_sub_cancel_left] using hspanC)
    (by simpa only [NNReal.coe_add,add_sub_cancel_left] using hspanS)
    (by simpa only [NNReal.coe_add,add_sub_cancel_left] using hHistory)
    (v+s) (lt_add_of_pos_right v hs) (by simpa only [add_comm] using add_lt_add_left hsh v) hqH hq1 hwidth1
    B1 hBDG1 A0 ν hA0 hν hjet p hp Bcur hBDGcur Bword hBDGword χ hχ hχ1 horder
    mass ρ lam ε tail η hmass hρ hρhalf hlam htail hη hρη
  have hl(ω:Ω):=(MovingNativeAverageTranslation.left_translation
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
    P haP h Z htarget hstop F hF hFm hΛ.le k v s ω hmass hρ.le)
  have hr(ω:Ω):=(MovingNativeAverageTranslation.right_translation
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
    P haP h Z htarget hstop F hF hFm hΛ.le k v s ω hmass hρ.le)
  simpa only [hl,hr] using he
end SHE.MovingNativeColumnEnergy
