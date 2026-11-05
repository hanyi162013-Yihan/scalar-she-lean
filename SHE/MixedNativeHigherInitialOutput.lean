module
public import SHE.MixedNativeHigherOriginalInputs
public import SHE.NativeOriginalOutputParameter
public import SHE.InitialNativePredictableAverages
public import SHE.MixedNativeHigherInitialCap
public import SHE.NativeCurrentWindowMeasure
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
namespace SHE.MixedNativeHigherInitialOutput
open MeasureTheory PredictableL2 NativeHeatObservation NativeObservationNaturality
open FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation StoppedItoInputs
open scoped NNReal ENNReal
local instance mixedNativeHigherInitialOutput_realSigma : MeasurableSpace RealL2 := borel _
local instance mixedNativeHigherInitialOutput_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance mixedNativeHigherInitialOutput_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance mixedNativeHigherInitialOutput_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance mixedNativeHigherInitialOutput_blockSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance mixedNativeHigherInitialOutput_blockBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
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


local instance mixedNativeHigherInitialOutput_circleSigma : MeasurableSpace CircleL2 := borel _
local instance mixedNativeHigherInitialOutput_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩



open Real AddCircle Set Filter WordRecursion ControlledProfile ControlledReferenceLevel SmoothCylinders UniformSmooth
  CutoffWordLevel CutoffWordHistories CutoffCarriers PhysicalScoreChain PhysicalChainArrays
  PhysicalParentGeometry CoveredHistoryGeometry CoveredControlledLaw ControlledOldIntervals
  ControlledFamilyProfileForest GaussianIncrement GaussianConvolution MeasurableGaussianScores
open ProfileStability ProfileL2
open HistoryProductMeasure
open scoped BigOperators
local instance mixedNativeHigherInitialOutput_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
local instance mixedNativeHigherInitialOutput_nativeSecond:SecondCountableTopology CircleL2:=
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

variable (hnull:NullCompleteFiltration.ContainsNullSets 𝓕 μ)(hJ:StandardFiniteIto.Universal 𝓕 μ H J)
variable (hAs:BoundedSmooth (fun z=>κ+aV z))
local instance mixedNativeHigherInitialOutput_spaceSigma:MeasurableSpace NativeKernelHaarColumns.Space:=borel _
local instance mixedNativeHigherInitialOutput_spaceBorel:BorelSpace NativeKernelHaarColumns.Space:=⟨rfl⟩

local notation "TT" t:max=>(show Icc (R).base (R).horizon from InitialRetainedTriangleEnergy.clippedTime h (t:ℝ))
local notation "Output"=>MixedNativeHigherInitialEnergy.output
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h F hF hFm
  J hIJ₀ hIJ₁ hnull hJ hAs
local notation "Row"=>InitialNativePredictableAverages.row
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h F hF hFm
local notation "Source0" T:max=>MixedNativeOriginalFourierRows.left
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP 0 (BT T) bot_le
  (ZZ T) (fun _ _=>le_rfl) (fun _ _=>le_rfl) F hF hFm
local notation "Source1" T:max=>MixedNativeOriginalFourierRows.right
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP 0 (BT T) bot_le
  (ZZ T) (fun _ _=>le_rfl) (fun _ _=>le_rfl) F hF hFm

def output(hL:1≤Λ){ρ:ℝ}(hρ:0≤ρ)(k:ℕ)(z:ℝ≥0×Ω):CircleL2:=
  if 0<z.1∧z.1≤h then Output hL hρ k (TT z.1) z.2 else 0
local notation "Clipped"=>output 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
  P haP h F hF hFm J hIJ₀ hIJ₁ hnull hJ hAs

theorem mass_eq(hL:1≤Λ){ρ:ℝ}(hρ:0≤ρ)(k:ℕ):
    (∫⁻t,∫⁻ω,ENNReal.ofReal (‖Clipped hL hρ k (t,ω)‖^2) ∂μ ∂timeMeasure h)=
      ∫⁻t in Ioc (0:ℝ) (h:ℝ),∫⁻ω,ENNReal.ofReal
        (‖MixedNativeHigherInitialCap.realOutput
          𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h F hF hFm
          J hIJ₀ hIJ₁ hnull hJ hAs hL hρ k t ω‖^2) ∂μ:=by
  rw [timeMeasure_lintegral]
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  have ht':0<t.toNNReal∧t.toNNReal≤h:=by
    constructor
    · exact Real.toNNReal_pos.mpr ht.1
    · exact (Real.toNNReal_le_iff_le_coe).mpr ht.2
  simp only [output,if_pos ht',MixedNativeHigherInitialCap.realOutput,
    Real.coe_toNNReal _ ht.1.le]

include hIJ₀ hIJ₁ hnull hJ haP in
theorem exists_identified(hA:P.coefficient=(fun z=>κ+aV z))
    (hlocal:StandardTerminalPastLocality J)(hL:1≤Λ){ρ:ℝ}(hρ:0<ρ)(hρhalf:ρ<1/2)
    (hhH:h≤H)(hH:(H:ℝ)≤1)(k:ℕ)
    (hsmall:ProfileStability.memoryConstant P.lower P.holder P.exponent*
      ProfileVolterra.powerConstant ((P.exponent-2)/4)*P.horizon^(P.exponent/4)≤1/2)
    (hsmallL2:ProfileStability.memoryConstant P.lower P.holder P.exponent*
      ProfileVolterra.powerConstant ((P.exponent-1)/4)*P.horizon^(P.exponent/4)≤1/2)
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
    (hfinite:(∫⁻t,∫⁻ω,ENNReal.ofReal (‖Clipped hL hρ.le k (t,ω)‖^2) ∂μ ∂νp)<∞):
    ∃Y:ℝ≥0×Ω→CircleL2,Measurable Y ∧
      (∀ᵐt∂νp,(fun ω=>Y (t,ω))=ᵐ[μ] (fun ω=>Clipped hL hρ.le k (t,ω))) ∧
      (∫⁻t,∫⁻ω,ENNReal.ofReal (‖Y (t,ω)‖^2) ∂μ ∂νp)=
        ∫⁻t,∫⁻ω,ENNReal.ofReal (‖Clipped hL hρ.le k (t,ω)‖^2) ∂μ ∂νp:=by
  classical
  have hΛ:0≤Λ:=zero_le_one.trans hL
  let Raw(a:ℂ→L[ℝ]ℝ)(l:ℤ)(z:ℝ≥0×(ℝ≥0×Ω)):Both RealHaarInput:=
    if 0<z.1∧z.1≤h then Row hΛ k hL hρ.le a l (TT z.1,z.2) else 0
  have hRaw(a:ℂ→L[ℝ]ℝ)(l:ℤ):
      StronglyMeasurable[((inferInstance:MeasurableSpace ℝ≥0).prod 𝓕.predictable)] (Raw a l):=by
    letI:MeasurableSpace (ℝ≥0×Ω):=𝓕.predictable
    have hT:Measurable (fun t:ℝ≥0=>TT t):=
      (InitialRetainedTriangleEnergy.clippedTime_measurable h).comp NNReal.continuous_coe.measurable
    have hm:Measurable (fun z:ℝ≥0×(ℝ≥0×Ω)=>(TT z.1,z.2)):=
      (hT.comp measurable_fst).prodMk measurable_snd
    have hs:MeasurableSet {z:ℝ≥0×(ℝ≥0×Ω)|0<z.1∧z.1≤h}:=
      (measurableSet_lt (α:=ℝ≥0) measurable_const measurable_fst).inter
        (measurableSet_le (α:=ℝ≥0) measurable_fst measurable_const)
    exact (((InitialNativePredictableAverages.row_predictable
      𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h F hF hFm
      hΛ k hL hρ.le a l).measurable.comp hm).ite hs measurable_const).stronglyMeasurable
  have hAvg:=InitialNativeAverageActual.average_initial_ae
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h F hF hFm hΛ
  have hAlign(T:Icc (R).base (R).horizon)(a:ℂ→L[ℝ]ℝ)(l:ℤ):
      (fun z:ℝ≥0×Ω=>WithLp.toLp 2
        (HilbertColumns.mapCLM (a.comp (NativeFourierNoiseRows.coefficient l)) ((Source0 T) k hL hρ.le z),
         HilbertColumns.mapCLM (a.comp (NativeFourierNoiseRows.coefficient l)) ((Source1 T) k hL hρ.le z)))
      =ᵐ[energyMeasure μ H] (fun z=>Row hΛ k hL hρ.le a l (T,z)):=by
    filter_upwards [Measure.quasiMeasurePreserving_snd.ae hAvg] with z hz
    rw [InitialNativePredictableAverages.row_original]
    by_cases hw:0<z.1∧z.1<BT T
    · have hw':0<(z.1:ℝ)∧(z.1:ℝ)<(T:ℝ):=by exact_mod_cast hw
      simp only [MixedNativeOriginalFourierRows.left,MixedNativeOriginalFourierRows.right,
        if_pos hw,InitialNativeColumnAverages.guardedLeft,InitialNativeColumnAverages.guardedRight,if_pos hw']
      rw [(hz T k z.1 Λ ρ hL hρ.le).1,(hz T k z.1 Λ ρ hL hρ.le).2]
    · have hw':¬(0<(z.1:ℝ)∧(z.1:ℝ)<(T:ℝ)):=by exact_mod_cast hw
      simp only [MixedNativeOriginalFourierRows.left,MixedNativeOriginalFourierRows.right,
        if_neg hw,InitialNativeColumnAverages.guardedLeft,InitialNativeColumnAverages.guardedRight,if_neg hw']
  have hex(t:ℝ≥0)(a:ℂ→L[ℝ]ℝ)(l:ℤ):∃input:Process (E:=Both RealHaarInput) 𝓕 μ H,
      J.integral input=ᵐ[μ] (fun ω=>a (fourierCoeff (Clipped hL hρ.le k (t,ω)) l)) ∧
      input=ᵐ[energyMeasure μ H] fun z=>Raw a l (t,z):=by
    by_cases ht:0<t∧t≤h
    · let T:Icc (R).base (R).horizon:=TT t
      have hclip:(T:ℝ)=(t:ℝ):=ClippedCovariance.clip_eq ⟨t.property,by exact_mod_cast ht.2⟩
      have hterm:BT T=t:=by ext;exact hclip
      have hThR:((BT T):ℝ)≤(h:ℝ):=by rw [hterm];exact_mod_cast ht.2
      obtain ⟨input,hout,hrow⟩:=MixedNativeHigherOriginalInputs.inputs
        𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S J hIJ₀ hIJ₁ hnull hJ
        P haP hAs 0 (BT T) bot_le (ZZ T) (fun _=>rfl) (fun _=>rfl) (fun _=>rfl) F hF hFm
        hsmall hA hlocal hL hρ hρhalf
        (by rw [hterm];exact ht.2.trans hhH)
        (by rw [hterm];exact (show (t:ℝ)≤(H:ℝ) from by exact_mod_cast ht.2.trans hhH).trans hH)
        (by rw [hterm];exact ht.1) k hsmallL2
        (by simpa only [NNReal.coe_zero,sub_zero] using hThR.trans hspan)
        (by simpa only [NNReal.coe_zero,sub_zero] using hThR.trans hspanF)
        (by simpa only [NNReal.coe_zero,sub_zero] using hThR.trans hspanC)
        (by simpa only [NNReal.coe_zero,sub_zero] using hThR.trans hspanS)
        (fun j hj=>by simpa only [NNReal.coe_zero,sub_zero] using hThR.trans (hHistory j hj))
        B1 hBDG1 A0 ν hA0 hν hjet p hp Bcur hBDGcur Bword hBDGword χ hχ hχ1 horder
        lam ε tail η hlam htail hη hρη a l
      refine ⟨input,?_,?_⟩
      · simpa only [output,if_pos ht,MixedNativeHigherInitialEnergy.output] using hout
      filter_upwards [hrow,hAlign T a l] with z hz ha
      dsimp only [Raw]
      rw [if_pos ht]
      exact hz.trans ha
    · refine ⟨0,?_,?_⟩
      · have hf:fourierCoeff (0:CircleL2) l=0:=by
          rw [←NativeMultiplierFourierIntegral.coefficient_apply]
          exact map_zero _
        filter_upwards [Lp.coeFn_zero ℝ 2 μ] with ω hω
        simp only [map_zero,output,if_neg ht,hf,map_zero]
        simpa only [Pi.zero_apply] using hω
      · filter_upwards [ae_eq_of_ae_eq_trim (Lp.coeFn_zero (Both RealHaarInput) 2
          ((energyMeasure μ H).trim (predictable_le_product 𝓕)))] with z hz
        dsimp only [Raw]
        rw [if_neg ht]
        simpa only [Pi.zero_apply] using hz
  choose r hrOut hrRows using fun t l=>hex t Complex.reCLM l
  choose i hiOut hiRows using fun t l=>hex t Complex.imCLM l
  apply NativeOriginalOutputParameter.exists_of_output_energy J hFubini νp r i
    (Raw Complex.reCLM) (Raw Complex.imCLM)
    (hRaw Complex.reCLM) (hRaw Complex.imCLM) hrRows hiRows
    (fun t ω=>Clipped hL hρ.le k (t,ω)) _ hfinite
  intro t
  filter_upwards [ae_all_iff.mpr (hrOut t),ae_all_iff.mpr (hiOut t)] with ω hr hi l
  rw [NativeMultiplierFourierIntegral.coefficient_apply]
  exact ⟨(hr l).symm,(hi l).symm⟩

end SHE.MixedNativeHigherInitialOutput

