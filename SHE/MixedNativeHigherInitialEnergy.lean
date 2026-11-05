module
public import SHE.MixedNativeHigherOriginalEnergy
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
namespace SHE.MixedNativeHigherInitialEnergy
open MeasureTheory PredictableL2 NativeHeatObservation NativeObservationNaturality
open FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation StoppedItoInputs
open scoped NNReal ENNReal
local instance mixedNativeHigherInitialEnergy_realSigma : MeasurableSpace RealL2 := borel _
local instance mixedNativeHigherInitialEnergy_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance mixedNativeHigherInitialEnergy_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance mixedNativeHigherInitialEnergy_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance mixedNativeHigherInitialEnergy_blockSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance mixedNativeHigherInitialEnergy_blockBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
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


local instance mixedNativeHigherInitialEnergy_circleSigma : MeasurableSpace CircleL2 := borel _
local instance mixedNativeHigherInitialEnergy_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩



open Real AddCircle Set Filter WordRecursion ControlledProfile ControlledReferenceLevel SmoothCylinders UniformSmooth
  CutoffWordLevel CutoffWordHistories CutoffCarriers PhysicalScoreChain PhysicalChainArrays
  PhysicalParentGeometry CoveredHistoryGeometry CoveredControlledLaw ControlledOldIntervals
  ControlledFamilyProfileForest GaussianIncrement GaussianConvolution MeasurableGaussianScores
open ProfileStability ProfileL2
open HistoryProductMeasure
open scoped BigOperators
local instance mixedNativeHigherInitialEnergy_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
local instance mixedNativeHigherInitialEnergy_nativeSecond:SecondCountableTopology CircleL2:=
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
local instance mixedNativeHigherInitialEnergy_spaceSigma:MeasurableSpace NativeKernelHaarColumns.Space:=borel _
local instance mixedNativeHigherInitialEnergy_spaceBorel:BorelSpace NativeKernelHaarColumns.Space:=⟨rfl⟩

/-- The actual kth paired native output on the variable initial strip. -/
def output(hL:1≤Λ){ρ:ℝ}(hρ:0≤ρ)(k:ℕ)(T:Icc (R).base (R).horizon)(ω:Ω):CircleL2:=
  MixedNativeHigherOriginalEnergy.value 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S J hIJ₀ hIJ₁ hnull hJ
    P hAs 0 (BT T) bot_le (ZZ T) (fun _=>rfl) (fun _=>rfl) F hF hFm hL hρ k ω
local notation "Output"=>output 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
  P haP h F hF hFm J hIJ₀ hIJ₁ hnull hJ hAs

include hIJ₀ hIJ₁ hnull hJ in
/-- The initial-strip original-J output energy is exactly the actual
jointly Borel initial-column energy. The one-event field identity is
used before integration; no variable-terminal AE diagonal is taken. -/
theorem energy(hA:P.coefficient=(fun z=>κ+aV z))
    (hlocal:StandardTerminalPastLocality J)(hL:1≤Λ){ρ:ℝ}(hρ:0<ρ)(hρhalf:ρ<1/2)
    (hhH:h≤H)(hH:(H:ℝ)≤1)(k:ℕ)(T:Icc (R).base (R).horizon)(hT:0<BT T)
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
    (lam ε tail η:ℝ)(hlam:1≤lam)(htail:tail≤ε*(2*((p-1:ℕ):ℝ)))(hη:0<η)(hρη:ρ+η<1):
    (∫⁻ω,ENNReal.ofReal (‖Output hL hρ.le k T ω‖^2) ∂μ)=
      ∫⁻q in Ioc (0:ℝ) ((BT T):ℝ),∫⁻ω,
        ENNReal.ofReal (‖Left (zero_le_one.trans hL) k hL hρ.le ((T,q.toNNReal),ω)‖^2+
          ‖Right (zero_le_one.trans hL) k hL hρ.le ((T,q.toNNReal),ω)‖^2) ∂μ:=by
  have hΛ:0≤Λ:=zero_le_one.trans hL
  have hTh:BT T≤h:=T.2.2
  have hThR:((BT T):ℝ)≤(h:ℝ):=by exact_mod_cast hTh
  have hTH:BT T≤H:=hTh.trans hhH
  let G:(ℝ≥0×Ω)→ℝ≥0∞:=fun z=>ENNReal.ofReal
    (‖(LeftA T) k z.1 hL hρ.le z.2‖^2+‖(RightA T) k z.1 hL hρ.le z.2‖^2)
  have hG:Measurable G:=
    (((MixedPastNativeCompleteColumns.left_time_measurable
      𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP 0 (BT T) bot_le
      (ZZ T) (fun _ _=>le_rfl) (fun _ _=>le_rfl) F hF hFm k hL hρ.le).norm.pow_const 2).add
      ((MixedPastNativeCompleteColumns.right_time_measurable
      𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP 0 (BT T) bot_le
      (ZZ T) (fun _ _=>le_rfl) (fun _ _=>le_rfl) F hF hFm hΛ k hL hρ.le).norm.pow_const 2)).ennreal_ofReal
  have he:=MixedNativeHigherOriginalEnergy.energy
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S J hIJ₀ hIJ₁ hnull hJ
    P haP hAs 0 (BT T) bot_le (ZZ T) (fun _=>rfl) (fun _=>rfl) (fun _=>rfl) F hF hFm
    hsmall hA hlocal hL hρ hρhalf hTH (le_trans (by exact_mod_cast hTH) hH) hT k hsmallL2
    (by simpa only [NNReal.coe_zero,sub_zero] using hThR.trans hspan)
    (by simpa only [NNReal.coe_zero,sub_zero] using hThR.trans hspanF)
    (by simpa only [NNReal.coe_zero,sub_zero] using hThR.trans hspanC)
    (by simpa only [NNReal.coe_zero,sub_zero] using hThR.trans hspanS)
    (fun j hj=>by simpa only [NNReal.coe_zero,sub_zero] using hThR.trans (hHistory j hj))
    B1 hBDG1 A0 ν hA0 hν hjet p hp Bcur hBDGcur Bword hBDGword χ hχ hχ1 horder
    lam ε tail η hlam htail hη hρη
  calc
    _=∫⁻z,(NativeGammaClock.window 0 (BT T)).indicator G z ∂energyMeasure μ H:=by
      unfold output
      rw [he]
      apply lintegral_congr
      intro z
      by_cases hw:0<z.1∧z.1<BT T
      · simp only [MixedNativeOriginalFourierRows.left,MixedNativeOriginalFourierRows.right,
          if_pos hw,indicator_of_mem (show z∈NativeGammaClock.window 0 (BT T) from hw),G]
      · simp only [MixedNativeOriginalFourierRows.left,MixedNativeOriginalFourierRows.right,
          if_neg hw,indicator_of_notMem (show z∉NativeGammaClock.window 0 (BT T) from hw),
          norm_zero,zero_pow (by norm_num:(2:ℕ)≠0),zero_add,ENNReal.ofReal_zero]
    _=∫⁻q in Ioc (0:ℝ) ((BT T):ℝ),∫⁻ω,G (q.toNNReal,ω) ∂μ:=by
      simpa only [NNReal.coe_zero,sub_zero,zero_add] using
        NativeCurrentWindowMeasure.product μ H 0 (BT T) hTH G hG
    _=_:=by
      apply lintegral_congr
      intro q
      apply lintegral_congr_ae
      filter_upwards [InitialNativeAverageActual.average_initial_ae
        𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h F hF hFm hΛ] with ω hω
      dsimp only [G]
      rw [(hω T k q.toNNReal Λ ρ hL hρ.le).1,(hω T k q.toNNReal Λ ρ hL hρ.le).2]

end SHE.MixedNativeHigherInitialEnergy

