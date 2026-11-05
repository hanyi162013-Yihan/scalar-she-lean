module
public import SHE.MixedNativeHigherOriginalInputs
public import SHE.NativeOriginalOutputParameter
public import SHE.MovingNativePredictableAverages
public import SHE.MixedNativeHigherMovingEnergy
public import SHE.NativeCurrentWindowMeasure
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
namespace SHE.MixedNativeHigherMovingOutput
open MeasureTheory PredictableL2 NativeHeatObservation NativeObservationNaturality
open FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation StoppedItoInputs
open scoped NNReal ENNReal
local instance mixedNativeHigherMovingOutput_realSigma : MeasurableSpace RealL2 := borel _
local instance mixedNativeHigherMovingOutput_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance mixedNativeHigherMovingOutput_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance mixedNativeHigherMovingOutput_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance mixedNativeHigherMovingOutput_blockSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance mixedNativeHigherMovingOutput_blockBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
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


local instance mixedNativeHigherMovingOutput_circleSigma : MeasurableSpace CircleL2 := borel _
local instance mixedNativeHigherMovingOutput_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩



open Real AddCircle Set Filter WordRecursion ControlledProfile ControlledReferenceLevel SmoothCylinders UniformSmooth
  CutoffWordLevel CutoffWordHistories CutoffCarriers PhysicalScoreChain PhysicalChainArrays
  PhysicalParentGeometry CoveredHistoryGeometry CoveredControlledLaw ControlledOldIntervals
  ControlledFamilyProfileForest GaussianIncrement GaussianConvolution MeasurableGaussianScores
open ProfileStability ProfileL2
open HistoryProductMeasure
open scoped BigOperators
local instance mixedNativeHigherMovingOutput_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
local instance mixedNativeHigherMovingOutput_nativeSecond:SecondCountableTopology CircleL2:=
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

variable (hnull:NullCompleteFiltration.ContainsNullSets 𝓕 μ)(hJ:StandardFiniteIto.Universal 𝓕 μ H J)
variable (hAs:BoundedSmooth (fun z=>κ+aV z))
variable (hrootStop:∀x,(Z.observations x 0).stop=(h:ℝ))
variable (hrootTarget:∀x,(Z.observations x 0).target=(h:ℝ))

local instance mixedNativeHigherMovingOutput_spaceSigma:MeasurableSpace NativeKernelHaarColumns.Space:=borel _
local instance mixedNativeHigherMovingOutput_spaceBorel:BorelSpace NativeKernelHaarColumns.Space:=⟨rfl⟩

local notation "Output"=>MixedNativeHigherMovingEnergy.output 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
  P h Z F hF hFm J hIJ₀ hIJ₁ hnull hJ hAs hrootStop hrootTarget

def output(hL:1≤Λ){ρ:ℝ}(hρ:0≤ρ)(k:ℕ)(z:ℝ≥0×Ω):CircleL2:=
  if z.1+h≤H then Output hL hρ k z.1 z.2 else 0
local notation "Clipped"=>output 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
  P h Z F hF hFm J hIJ₀ hIJ₁ hnull hJ hAs hrootStop hrootTarget
local notation "Row"=>MovingNativePredictableAverages.row
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h Z htarget hstop F hF hFm

theorem mass_eq(hL:1≤Λ){ρ:ℝ}(hρ:0≤ρ)(k:ℕ)(hh:h≤H):
    (∫⁻v,∫⁻ω,ENNReal.ofReal (‖Clipped hL hρ k (v,ω)‖^2) ∂μ ∂timeMeasure (H-h))=
      ∫⁻v in Ioc (0:ℝ) ((H:ℝ)-(h:ℝ)),∫⁻ω,
        ENNReal.ofReal (‖Output hL hρ k v.toNNReal ω‖^2) ∂μ:=by
  rw [timeMeasure_lintegral,NNReal.coe_sub hh]
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with v hv
  have hb:v.toNNReal+h≤H:=by
    apply NNReal.coe_le_coe.mp
    rw [NNReal.coe_add,Real.coe_toNNReal _ hv.1.le]
    linarith [hv.2]
  simp only [output,if_pos hb]

include hIJ₀ hIJ₁ hnull hJ hrootStop hrootTarget haP htarget hstop in
/-- The actual kth paired output has a Borel version on the common
past/sample measure. Its coordinates remain the SAME original J.
The finite energy here is supplied by the separately checked actual
moving clock estimate, not by an assumed stochastic output version. -/
theorem exists_identified(hA:P.coefficient=(fun z=>κ+aV z))
    (hlocal:StandardTerminalPastLocality J)(hL:1≤Λ){ρ:ℝ}(hρ:0<ρ)(hρhalf:ρ<1/2)
    (hpos:0<h)(hH:(H:ℝ)≤1)(k:ℕ)
    (hsmall:ProfileStability.memoryConstant P.lower P.holder P.exponent*
      ProfileVolterra.powerConstant ((P.exponent-2)/4)*P.horizon^(P.exponent/4)≤1/2)
    (hsmallL2:ProfileStability.memoryConstant P.lower P.holder P.exponent*
      ProfileVolterra.powerConstant ((P.exponent-1)/4)*P.horizon^(P.exponent/4)≤1/2)
    (hcenter:∀x,(Z.observations x 0).center=x)
    (hspan:(h:ℝ)≤P.horizon)
    (hspanF:(h:ℝ)≤NativeUniversalConstants.rowHorizon (1+k))
    (hspanC:(h:ℝ)≤4*Real.pi^2*NativeUniversalConstants.currentHorizon.{0} (1+k) (by omega))
    (hspanS:(h:ℝ)≤UniformFutureProfileScores.horizon (1+k))
    (hHistory:∀j,j<k→(h:ℝ)≤uniformHorizon 1 j)
    (B1:ℝ≥0)(hBDG1:StandardTerminalBDGPower 1 J B1)
    (A0 ν:ℝ)(hA0:0≤A0)(hν:0≤ν)
    (hjet:∀x j,j≤k→∀z,‖iteratedFDeriv ℝ j (F x) z‖≤A0*ν^j)
    (p:ℕ)(hp:0<p)(Bcur:ℝ≥0)(hBDGcur:StandardTerminalBDGPower (p*(k+2)) J Bcur)
    (Bword:ℝ≥0)(hBDGword:StandardTerminalBDGPower (k+2) J Bword)
    (χ:ℝ)(hχ:0≤χ)(hχ1:χ<1)(horder:1≤(p:ℝ)*(1-χ))
    (lam ε tail η:ℝ)(hlam:1≤lam)(htail:tail≤ε*(2*((p-1:ℕ):ℝ)))(hη:0<η)(hρη:ρ+η<1)
    (νp:Measure ℝ≥0)[SFinite νp](hFubini:StandardItoParameterFubini J)
    (hfinite:(∫⁻v,∫⁻ω,ENNReal.ofReal (‖Clipped hL hρ.le k (v,ω)‖^2) ∂μ ∂νp)<∞):
    ∃Y:ℝ≥0×Ω→CircleL2,Measurable Y ∧
      (∀ᵐv∂νp,(fun ω=>Y (v,ω))=ᵐ[μ] (fun ω=>Clipped hL hρ.le k (v,ω))) ∧
      (∫⁻v,∫⁻ω,ENNReal.ofReal (‖Y (v,ω)‖^2) ∂μ ∂νp)=
        ∫⁻v,∫⁻ω,ENNReal.ofReal (‖Clipped hL hρ.le k (v,ω)‖^2) ∂μ ∂νp:=by
  classical
  have hΛ:0≤Λ:=zero_le_one.trans hL
  let Raw(a:ℂ→L[ℝ]ℝ)(l:ℤ)(z:ℝ≥0×(ℝ≥0×Ω)):Both RealHaarInput:=
    if z.1+h≤H then Row hΛ k hL hρ.le a l z else 0
  have hRaw(a:ℂ→L[ℝ]ℝ)(l:ℤ):
      StronglyMeasurable[((inferInstance:MeasurableSpace ℝ≥0).prod 𝓕.predictable)] (Raw a l):=by
    letI:MeasurableSpace (ℝ≥0×Ω):=𝓕.predictable
    have hs:MeasurableSet {z:ℝ≥0×(ℝ≥0×Ω)|z.1+h≤H}:=
      measurableSet_le (measurable_fst.add_const h) measurable_const
    exact ((MovingNativePredictableAverages.row_predictable
      𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h Z htarget hstop F hF hFm
      hΛ k hL hρ.le a l).measurable.ite hs measurable_const).stronglyMeasurable
  have hex(v:ℝ≥0)(a:ℂ→L[ℝ]ℝ)(l:ℤ):∃input:Process (E:=Both RealHaarInput) 𝓕 μ H,
      J.integral input=ᵐ[μ] (fun ω=>a (fourierCoeff (Clipped hL hρ.le k (v,ω)) l)) ∧
      input=ᵐ[energyMeasure μ H] fun z=>Raw a l (v,z):=by
    by_cases hv:v+h≤H
    · obtain ⟨input,hout,hrow⟩:=MixedNativeHigherOriginalInputs.inputs
        𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S J hIJ₀ hIJ₁ hnull hJ
        P haP hAs v (v+h) le_self_add (ZT v)
        (MixedNativeHigherMovingEnergy.rootStop h Z hrootStop v)
        (MixedNativeHigherMovingEnergy.rootTarget h Z hrootTarget v)
        hcenter F hF hFm hsmall hA hlocal hL hρ hρhalf hv
        ((by exact_mod_cast hv:((v+h):ℝ)≤(H:ℝ)).trans hH) (lt_add_of_pos_right v hpos) k hsmallL2
        (by simpa only [NNReal.coe_add,add_sub_cancel_left] using hspan)
        (by simpa only [NNReal.coe_add,add_sub_cancel_left] using hspanF)
        (by simpa only [NNReal.coe_add,add_sub_cancel_left] using hspanC)
        (by simpa only [NNReal.coe_add,add_sub_cancel_left] using hspanS)
        (fun j hj=>by simpa only [NNReal.coe_add,add_sub_cancel_left] using hHistory j hj)
        B1 hBDG1 A0 ν hA0 hν hjet p hp Bcur hBDGcur Bword hBDGword χ hχ hχ1 horder
        lam ε tail η hlam htail hη hρη a l
      refine ⟨input,?_,?_⟩
      · simpa only [output,if_pos hv,MixedNativeHigherMovingEnergy.output] using hout
      filter_upwards [hrow] with z hz
      dsimp only [Raw]
      rw [if_pos hv,MovingNativePredictableAverages.row_original]
      exact hz
    · refine ⟨0,?_,?_⟩
      · have hf:fourierCoeff (0:CircleL2) l=0:=by
          rw [←NativeMultiplierFourierIntegral.coefficient_apply]
          exact map_zero _
        filter_upwards [Lp.coeFn_zero ℝ 2 μ] with ω hω
        change (J.integral (0:Process (E:=Both RealHaarInput) 𝓕 μ H)) ω=
          a (fourierCoeff (Clipped hL hρ.le k (v,ω)) l)
        simp only [map_zero,output,if_neg hv,hf,map_zero]
        simpa only [Pi.zero_apply] using hω
      · filter_upwards [ae_eq_of_ae_eq_trim (Lp.coeFn_zero (Both RealHaarInput) 2
          ((energyMeasure μ H).trim (predictable_le_product 𝓕)))] with z hz
        change (0:Process (E:=Both RealHaarInput) 𝓕 μ H) z=Raw a l (v,z)
        dsimp only [Raw]
        rw [if_neg hv]
        simpa only [Pi.zero_apply] using hz
  choose r hrOut hrRows using fun v l=>hex v Complex.reCLM l
  choose i hiOut hiRows using fun v l=>hex v Complex.imCLM l
  apply NativeOriginalOutputParameter.exists_of_output_energy J hFubini νp r i
    (Raw Complex.reCLM) (Raw Complex.imCLM)
    (hRaw Complex.reCLM) (hRaw Complex.imCLM) hrRows hiRows
    (fun v ω=>Clipped hL hρ.le k (v,ω)) _ hfinite
  intro v
  filter_upwards [ae_all_iff.mpr (hrOut v),ae_all_iff.mpr (hiOut v)] with ω hr hi l
  rw [NativeMultiplierFourierIntegral.coefficient_apply]
  exact ⟨(hr l).symm,(hi l).symm⟩

end SHE.MixedNativeHigherMovingOutput
