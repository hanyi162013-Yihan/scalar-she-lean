module
public import SHE.InitialNativeAverageActual
public import SHE.InitialNativeColumnActual
public import SHE.InitialNativeOldCube
public import SHE.InitialNativeColumnAverages
public import SHE.MixedPastNativeCompleteColumns
public import SHE.InitialNativeColumns
public import SHE.MixedPastNativeKernelSemigroup
public import SHE.MixedPastNativeOldTimeEnergy
public import SHE.MixedPastSignedEndpointFields
public import SHE.NativeKernelCongruence
public import SHE.MixedNativePairInitial
public import SHE.ControlledScalarReference
public import SHE.WordRootState
public import SHE.MovingNativeFields
public import SHE.ZeroDirectionProfile
public import SHE.MixedPastNativeTimeFields
public import SHE.NativeRowTimeShift

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
set_option quotPrecheck false
namespace SHE.InitialNativeColumnEnergy
open MeasureTheory PredictableL2 NativeHeatObservation NativeObservationNaturality
open FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation StoppedItoInputs
open scoped NNReal ENNReal
local instance movingNativeKernelFields_realSigma : MeasurableSpace RealL2 := borel _
local instance movingNativeKernelFields_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance movingNativeKernelFields_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance movingNativeKernelFields_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance movingNativeKernelFields_blockSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance movingNativeKernelFields_blockBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
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


local instance movingNativeKernelFields_circleSigma : MeasurableSpace CircleL2 := borel _
local instance movingNativeKernelFields_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩



open Real AddCircle Set Filter WordRecursion ControlledProfile ControlledReferenceLevel SmoothCylinders UniformSmooth
  CutoffWordLevel CutoffWordHistories CutoffCarriers PhysicalScoreChain PhysicalChainArrays
  PhysicalParentGeometry CoveredHistoryGeometry CoveredControlledLaw ControlledOldIntervals
  ControlledFamilyProfileForest GaussianIncrement GaussianConvolution MeasurableGaussianScores
open ProfileStability ProfileL2
open HistoryProductMeasure
open scoped BigOperators
local instance movingNativeKernelFields_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
local instance movingNativeKernelFields_nativeSecond:SecondCountableTopology CircleL2:=
  (_root_.fourierBasis (T:=2*Real.pi)).repr.toHomeomorph.secondCountableTopology
variable (P:CanonicalCovariance.ProfileParameters)(haP:BoundedSmooth P.coefficient)
variable (h:ℝ≥0)
variable (F:HeatCircle→WordRecursion.State 1→ℝ)(hF:UniformBoundedSmooth F)
variable (hFm:Measurable (fun z:HeatCircle×WordRecursion.State 1=>F z.1 z.2))
local notation "R"=>InitialNativeKernelFields.referenceData Λ u₀ P haP h
local notation "BT" T:max=>InitialNativeKernelFibre.terminal Λ u₀ P haP h T
local notation "ZZ" T:max=>ControlledScalarReference.observations (BT T)
local notation "LeftA" T:max=>MixedPastNativeCompleteColumns.left 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP
  0 (BT T) bot_le (ZZ T) (fun _ _=>le_rfl) (fun _ _=>le_rfl) F hF hFm
local notation "RightA" T:max=>MixedPastNativeCompleteColumns.right 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP
  0 (BT T) bot_le (ZZ T) (fun _ _=>le_rfl) (fun _ _=>le_rfl) F hF hFm
local notation "Left"=>InitialNativeColumnAverages.left 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h F hF hFm
local notation "Right"=>InitialNativeColumnAverages.right 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h F hF hFm

variable (J:StandardTerminalIto (C:=Both RealHaarInput) (E:=ℝ) 𝓕 μ H)
variable (hIJ₀:StandardScalarNaturality I₀ (leftIntegral 𝓕 μ H J))
variable (hIJ₁:StandardScalarNaturality I₁ (rightIntegral 𝓕 μ H J))

/-- Actual common initial data have exactly zero initial difference
energy. This is derived from both original mild initial conditions. -/
theorem initial_energy_zero:
    (∫ω,‖S.second 0 ω-S.first 0 ω‖^2 ∂μ)=0:=by
  have he:(fun ω=>‖S.second 0 ω-S.first 0 ω‖^2)=ᵐ[μ] (fun _=>0):=by
    filter_upwards [MixedNativeAdditiveResidualPair.first_zero
      𝓕 μ H hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S,
      MixedNativeAdditiveResidualPair.second_zero
      𝓕 μ H hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S] with ω hU hV
    simp only [hU,hV,sub_self,norm_zero,zero_pow (by norm_num:(2:ℕ)≠0)]
  rw [integral_congr_ae he,integral_zero]

include hIJ₀ hIJ₁ in
/-- The variable-terminal initial-strip Borel fields satisfy the full
actual column-energy bound. No initial strip or terminal endpoint is
identified by an uncountable collection of exceptional events. -/
theorem energy(k:ℕ)(hΛ:0<Λ)(hlocal:StandardTerminalPastLocality J)
    (hsmallPoint:ProfileStability.memoryConstant P.lower P.holder P.exponent*
      ProfileVolterra.powerConstant ((P.exponent-2)/4)*P.horizon^(P.exponent/4)≤1/2)
    (hsmallL2:ProfileStability.memoryConstant P.lower P.holder P.exponent*
      ProfileVolterra.powerConstant ((P.exponent-1)/4)*P.horizon^(P.exponent/4)≤1/2)
    (hspan:(h:ℝ)≤P.horizon)
    (hspanF:(h:ℝ)≤NativeUniversalConstants.rowHorizon (1+k))
    (hspanC:(h:ℝ)≤4*Real.pi^2*NativeUniversalConstants.currentHorizon.{0} (1+k) (by omega))
    (hspanS:(h:ℝ)≤UniformFutureProfileScores.horizon (1+k))
    (hHistory:∀j,j<k→(h:ℝ)≤uniformHorizon 1 j)
    (T:Icc (R).base (R).horizon)(q:ℝ≥0)(hq:0<q)(hqT:q<BT T)
    (hhH:h≤H)(hH:(H:ℝ)≤1)
    (B1:ℝ≥0)(hBDG1:StandardTerminalBDGPower 1 J B1)
    (A0 ν:ℝ)(hA0:0≤A0)(hν:0≤ν)
    (hjet:∀x j,j≤k→∀z,‖iteratedFDeriv ℝ j (F x) z‖≤A0*ν^j)
    (p:ℕ)(hp:0<p)(Bcur:ℝ≥0)(hBDGcur:StandardTerminalBDGPower (p*(k+2)) J Bcur)
    (Bword:ℝ≥0)(hBDGword:StandardTerminalBDGPower (k+2) J Bword)
    (χ:ℝ)(hχ:0≤χ)(hχ1:χ<1)(horder:1≤(p:ℝ)*(1-χ))
    (mass ρ lam ε tail η:ℝ)(hmass:1≤mass)(hρ:0<ρ)(hρhalf:ρ<1/2)
    (hlam:1≤lam)(htail:tail≤ε*(2*((p-1:ℕ):ℝ)))(hη:0<η)(hρη:ρ+η<1):
    Integrable (fun ω=>‖Left hΛ.le k hmass hρ.le ((T,q),ω)‖^2) μ ∧
      Integrable (fun ω=>‖Right hΛ.le k hmass hρ.le ((T,q),ω)‖^2) μ ∧
      (∫ω,‖Left hΛ.le k hmass hρ.le ((T,q),ω)‖^2 ∂μ)+
        (∫ω,‖Right hΛ.le k hmass hρ.le ((T,q),ω)‖^2 ∂μ)≤
        4*(MixedPastNativeCompleteColumns.commonBudget
          𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P 0 (BT T) k q A0 ν ρ χ p Bcur Bword)^2+
        2*(MixedPastNativeCompleteColumns.signedBudget
          𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P 0 (BT T)
          k q A0 ν mass ρ lam ε tail η hmass hρ hρhalf p Bcur)^2:=by
  have hTh:BT T≤h:=T.2.2
  have hThR:((BT T):ℝ)≤(h:ℝ):=by exact_mod_cast hTh
  have hqH:q≤H:=hqT.le.trans (hTh.trans hhH)
  have hq1:(q:ℝ)≤1:=le_trans (by exact_mod_cast hqH) hH
  have hwidth1:((BT T):ℝ)-(q:ℝ)≤1:=by
    have hTr:((BT T):ℝ)≤1:=le_trans (by exact_mod_cast (hTh.trans hhH)) hH
    linarith [q.2]
  have he:=MixedPastNativeCompleteColumns.energy
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S J hIJ₀ hIJ₁
    P haP 0 (BT T) bot_le (ZZ T) (fun _ _=>le_rfl) (fun _ _=>le_rfl) F hF hFm
    k hΛ hlocal hsmallPoint hsmallL2 (fun _ _=>rfl) (fun _ _=>rfl) (fun _ _=>rfl)
    (by simpa only [NNReal.coe_zero,sub_zero] using hThR.trans hspan)
    (by simpa only [NNReal.coe_zero,sub_zero] using hThR.trans hspanF)
    (by simpa only [NNReal.coe_zero,sub_zero] using hThR.trans hspanC)
    (by simpa only [NNReal.coe_zero,sub_zero] using hThR.trans hspanS)
    (by intro j hj;simpa only [NNReal.coe_zero,sub_zero] using hThR.trans (hHistory j hj))
    q hq hqT hqH hq1 hwidth1
    B1 hBDG1 A0 ν hA0 hν hjet p hp Bcur hBDGcur Bword hBDGword χ hχ hχ1 horder
    mass ρ lam ε tail η hmass hρ hρhalf hlam htail hη hρη
  have ha:=InitialNativeAverageActual.average_initial_ae
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h F hF hFm hΛ.le
  have hl:(fun ω=>‖(LeftA T) k q hmass hρ.le ω‖^2)=ᵐ[μ]
      (fun ω=>‖Left hΛ.le k hmass hρ.le ((T,q),ω)‖^2):=ha.mono (fun ω hω=>
    congrArg (fun C:NativeKernelHaarColumns.Space=>‖C‖^2) (hω T k q mass ρ hmass hρ.le).1)
  have hr:(fun ω=>‖(RightA T) k q hmass hρ.le ω‖^2)=ᵐ[μ]
      (fun ω=>‖Right hΛ.le k hmass hρ.le ((T,q),ω)‖^2):=ha.mono (fun ω hω=>
    congrArg (fun C:NativeKernelHaarColumns.Space=>‖C‖^2) (hω T k q mass ρ hmass hρ.le).2)
  refine ⟨he.1.congr hl,he.2.1.congr hr,?_⟩
  rw [←integral_congr_ae hl,←integral_congr_ae hr]
  exact he.2.2
end SHE.InitialNativeColumnEnergy
