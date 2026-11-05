module
public import SHE.MixedNativeHigherOriginalEnergy
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
namespace SHE.MixedNativeHigherMovingEnergy
open MeasureTheory PredictableL2 NativeHeatObservation NativeObservationNaturality
open FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation StoppedItoInputs
open scoped NNReal ENNReal
local instance mixedNativeHigherMovingEnergy_realSigma : MeasurableSpace RealL2 := borel _
local instance mixedNativeHigherMovingEnergy_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance mixedNativeHigherMovingEnergy_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance mixedNativeHigherMovingEnergy_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance mixedNativeHigherMovingEnergy_blockSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance mixedNativeHigherMovingEnergy_blockBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
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


local instance mixedNativeHigherMovingEnergy_circleSigma : MeasurableSpace CircleL2 := borel _
local instance mixedNativeHigherMovingEnergy_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩



open Real AddCircle Set Filter WordRecursion ControlledProfile ControlledReferenceLevel SmoothCylinders UniformSmooth
  CutoffWordLevel CutoffWordHistories CutoffCarriers PhysicalScoreChain PhysicalChainArrays
  PhysicalParentGeometry CoveredHistoryGeometry CoveredControlledLaw ControlledOldIntervals
  ControlledFamilyProfileForest GaussianIncrement GaussianConvolution MeasurableGaussianScores
open ProfileStability ProfileL2
open HistoryProductMeasure
open scoped BigOperators
local instance mixedNativeHigherMovingEnergy_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
local instance mixedNativeHigherMovingEnergy_nativeSecond:SecondCountableTopology CircleL2:=
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

local instance mixedNativeHigherMovingEnergy_spaceSigma:MeasurableSpace NativeKernelHaarColumns.Space:=borel _
local instance mixedNativeHigherMovingEnergy_spaceBorel:BorelSpace NativeKernelHaarColumns.Space:=⟨rfl⟩

def rootStop(v:ℝ≥0)(x:HeatCircle):((ZT v).observations x 0).stop=((v+h):ℝ):=by
  change (Z.observations x 0).stop+(v:ℝ)=((v+h):ℝ)
  rw [hrootStop]
  exact add_comm _ _

def rootTarget(v:ℝ≥0)(x:HeatCircle):((ZT v).observations x 0).target=((v+h):ℝ):=by
  change (Z.observations x 0).target+(v:ℝ)=((v+h):ℝ)
  rw [hrootTarget]
  exact add_comm _ _

/-- The literal kth paired original noise for the completed physical
window [v,v+h]. No joint choice of stochastic versions is implicit. -/
def output(hL:1≤Λ){ρ:ℝ}(hρ:0≤ρ)(k:ℕ)(v:ℝ≥0)(ω:Ω):CircleL2:=
  MixedNativeHigherOriginalEnergy.value 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S J hIJ₀ hIJ₁ hnull hJ
    P hAs v (v+h) le_self_add (ZT v) (rootStop h Z hrootStop v) (rootTarget h Z hrootTarget v) F hF hFm hL hρ k ω
local notation "Output"=>output 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
  P h Z F hF hFm J hIJ₀ hIJ₁ hnull hJ hAs hrootStop hrootTarget

include hIJ₀ hIJ₁ hnull hJ hrootStop hrootTarget in
/-- Exact original-J output energy on a moving completed window,
expressed on the fixed relative-current clock and the genuinely Borel
complete moving columns. This is an equality, including the signed leg. -/
theorem energy(hA:P.coefficient=(fun z=>κ+aV z))
    (hlocal:StandardTerminalPastLocality J)(hL:1≤Λ){ρ:ℝ}(hρ:0<ρ)(hρhalf:ρ<1/2)
    (hpos:0<h)(v:ℝ≥0)(hvhH:v+h≤H)(hH:(H:ℝ)≤1)(k:ℕ)
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
    (lam ε tail η:ℝ)(hlam:1≤lam)(htail:tail≤ε*(2*((p-1:ℕ):ℝ)))(hη:0<η)(hρη:ρ+η<1):
    (∫⁻ω,ENNReal.ofReal (‖Output hL hρ.le k v ω‖^2) ∂μ)=
      ∫⁻s in Ioc (0:ℝ) (h:ℝ),∫⁻ω,
        ENNReal.ofReal (‖Left (zero_le_one.trans hL) k hL hρ.le ((v,s.toNNReal),ω)‖^2+
          ‖Right (zero_le_one.trans hL) k hL hρ.le ((v,s.toNNReal),ω)‖^2) ∂μ:=by
  have hΛ:0≤Λ:=zero_le_one.trans hL
  let G:(ℝ≥0×Ω)→ℝ≥0∞:=fun z=>ENNReal.ofReal
    (‖(LeftA v) k z.1 hL hρ.le z.2‖^2+‖(RightA v) k z.1 hL hρ.le z.2‖^2)
  have hG:Measurable G:=
    (((MixedPastNativeCompleteColumns.left_time_measurable
      𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP v (v+h) le_self_add
      (ZT v) (HT v) (HS v) F hF hFm k hL hρ.le).norm.pow_const 2).add
      ((MixedPastNativeCompleteColumns.right_time_measurable
      𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP v (v+h) le_self_add
      (ZT v) (HT v) (HS v) F hF hFm hΛ k hL hρ.le).norm.pow_const 2)).ennreal_ofReal
  have he:=MixedNativeHigherOriginalEnergy.energy
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S J hIJ₀ hIJ₁ hnull hJ
    P haP hAs v (v+h) le_self_add (ZT v) (rootStop h Z hrootStop v) (rootTarget h Z hrootTarget v)
    hcenter F hF hFm hsmall hA hlocal hL hρ hρhalf hvhH
    ((by exact_mod_cast hvhH:((v+h):ℝ)≤(H:ℝ)).trans hH) (lt_add_of_pos_right v hpos) k hsmallL2
    (by simpa only [NNReal.coe_add,add_sub_cancel_left] using hspan)
    (by simpa only [NNReal.coe_add,add_sub_cancel_left] using hspanF)
    (by simpa only [NNReal.coe_add,add_sub_cancel_left] using hspanC)
    (by simpa only [NNReal.coe_add,add_sub_cancel_left] using hspanS)
    (fun j hj=>by simpa only [NNReal.coe_add,add_sub_cancel_left] using hHistory j hj)
    B1 hBDG1 A0 ν hA0 hν hjet p hp Bcur hBDGcur Bword hBDGword χ hχ hχ1 horder
    lam ε tail η hlam htail hη hρη
  calc
    _=∫⁻z,(NativeGammaClock.window v (v+h)).indicator G z ∂energyMeasure μ H:=by
      unfold output
      rw [he]
      apply lintegral_congr
      intro z
      by_cases hw:v<z.1∧z.1<v+h
      · simp only [MixedNativeOriginalFourierRows.left,MixedNativeOriginalFourierRows.right,
          if_pos hw,indicator_of_mem (show z∈NativeGammaClock.window v (v+h) from hw),G]
      · simp only [MixedNativeOriginalFourierRows.left,MixedNativeOriginalFourierRows.right,
          if_neg hw,indicator_of_notMem (show z∉NativeGammaClock.window v (v+h) from hw),
          norm_zero,zero_pow (by norm_num:(2:ℕ)≠0),zero_add,ENNReal.ofReal_zero]
    _=∫⁻s in Ioc (0:ℝ) (h:ℝ),∫⁻ω,G (((v:ℝ)+s).toNNReal,ω) ∂μ:=by
      simpa only [NNReal.coe_add,add_sub_cancel_left] using
        NativeCurrentWindowMeasure.product μ H v (v+h) hvhH G hG
    _=_:=by
      rw [←restrict_Ioo_eq_restrict_Ioc]
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
      have hq:((v:ℝ)+s).toNNReal=v+s.toNNReal:=by
        ext
        rw [NNReal.coe_add,Real.coe_toNNReal s hs.1.le]
        exact Real.coe_toNNReal ((v:ℝ)+s) (add_nonneg v.property hs.1.le)
      rw [hq]
      apply lintegral_congr
      intro ω
      dsimp only [G]
      rw [MovingNativeAverageTranslation.left_translation
        𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h Z htarget hstop F hF hFm
        hΛ k v s.toNNReal ω hL hρ.le,
        MovingNativeAverageTranslation.right_translation
        𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h Z htarget hstop F hF hFm
        hΛ k v s.toNNReal ω hL hρ.le]

end SHE.MixedNativeHigherMovingEnergy

