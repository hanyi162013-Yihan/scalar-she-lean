module
public import SHE.MixedNativeHigherMovingEnergy
public import SHE.MovingNativeFourTermEnergy

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2500000
set_option quotPrecheck false
namespace SHE.MixedNativeHigherMovingCap
open MeasureTheory PredictableL2 NativeHeatObservation NativeObservationNaturality
open FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation StoppedItoInputs
open scoped NNReal ENNReal
local instance mixedNativeHigherMovingCap_realSigma : MeasurableSpace RealL2 := borel _
local instance mixedNativeHigherMovingCap_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance mixedNativeHigherMovingCap_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance mixedNativeHigherMovingCap_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance mixedNativeHigherMovingCap_blockSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance mixedNativeHigherMovingCap_blockBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
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


local instance mixedNativeHigherMovingCap_circleSigma : MeasurableSpace CircleL2 := borel _
local instance mixedNativeHigherMovingCap_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩



open Real AddCircle Set Filter WordRecursion ControlledProfile ControlledReferenceLevel SmoothCylinders UniformSmooth
  CutoffWordLevel CutoffWordHistories CutoffCarriers PhysicalScoreChain PhysicalChainArrays
  PhysicalParentGeometry CoveredHistoryGeometry CoveredControlledLaw ControlledOldIntervals
  ControlledFamilyProfileForest GaussianIncrement GaussianConvolution MeasurableGaussianScores
open ProfileStability ProfileL2
open HistoryProductMeasure
open scoped BigOperators
local instance mixedNativeHigherMovingCap_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
local instance mixedNativeHigherMovingCap_nativeSecond:SecondCountableTopology CircleL2:=
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

local instance mixedNativeHigherMovingCap_spaceSigma:MeasurableSpace NativeKernelHaarColumns.Space:=borel _
local instance mixedNativeHigherMovingCap_spaceBorel:BorelSpace NativeKernelHaarColumns.Space:=⟨rfl⟩


local notation "Output"=>MixedNativeHigherMovingEnergy.output 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
  P h Z F hF hFm J hIJ₀ hIJ₁ hnull hJ hAs hrootStop hrootTarget
local notation "Env"=>MovingNativeFourTermEnergy.envelope 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P

include haP htarget hstop hIJ₀ hIJ₁ hnull hJ hrootStop hrootTarget in
/-- The actual original-J kth output is bounded by the literal four
energy-clock cap. All source-column applicability is discharged. -/
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
    (∫⁻ω,ENNReal.ofReal (‖Output hL hρ.le k v ω‖^2) ∂μ)≤
      ∫⁻s in Ioc (0:ℝ) (h:ℝ),ENNReal.ofReal
        (Env v h s.toNNReal k A0 ν Λ ρ χ lam ε tail η hL hρ hρhalf p Bcur Bword):=by
  rw [MixedNativeHigherMovingEnergy.energy
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h Z htarget hstop F hF hFm
    J hIJ₀ hIJ₁ hnull hJ hAs hrootStop hrootTarget hA hlocal hL hρ hρhalf hpos v hvhH hH k
    hsmall hsmallL2 hcenter hspan hspanF hspanC hspanS hHistory B1 hBDG1 A0 ν hA0 hν hjet
    p hp Bcur hBDGcur Bword hBDGword χ hχ hχ1 horder lam ε tail η hlam htail hη hρη]
  rw [←restrict_Ioo_eq_restrict_Ioc]
  apply lintegral_mono_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
  have hs0:0<s.toNNReal:=Real.toNNReal_pos.mpr hs.1
  have hsh:s.toNNReal<h:=by
    apply NNReal.coe_lt_coe.mp
    simpa only [Real.coe_toNNReal _ hs.1.le] using hs.2
  have ht:∀x i,(Z.observations x i).target=(h:ℝ):=by
    intro x i
    have hi:i=0:=Subsingleton.elim _ _
    simpa only [hi] using hrootTarget x
  have hσ:∀x i,(Z.observations x i).stop=(h:ℝ):=by
    intro x i
    have hi:i=0:=Subsingleton.elim _ _
    simpa only [hi] using hrootStop x
  have hx:∀x i,(Z.observations x i).center=x:=by
    intro x i
    have hi:i=0:=Subsingleton.elim _ _
    simpa only [hi] using hcenter x
  obtain ⟨hi0,hi1,hcap⟩:=MovingNativeFourTermEnergy.energy
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
    P haP h Z htarget hstop F hF hFm J hIJ₀ hIJ₁ k (zero_lt_one.trans_le hL) hlocal hsmall hsmallL2
    ht hσ hx hspan hspanF hspanC hspanS hHistory
    v s.toNNReal hs0 hsh hvhH hH B1 hBDG1 A0 ν hA0 hν hjet
    p hp Bcur hBDGcur Bword hBDGword χ hχ hχ1 horder
    Λ ρ lam ε tail η hL hρ hρhalf hlam htail hη hρη
  calc
    _=ENNReal.ofReal ((∫ω,‖Left (zero_le_one.trans hL) k hL hρ.le ((v,s.toNNReal),ω)‖^2 ∂μ)+
        (∫ω,‖Right (zero_le_one.trans hL) k hL hρ.le ((v,s.toNNReal),ω)‖^2 ∂μ)):=by
      have hi:Integrable (fun ω=>‖Left (zero_le_one.trans hL) k hL hρ.le ((v,s.toNNReal),ω)‖^2+
          ‖Right (zero_le_one.trans hL) k hL hρ.le ((v,s.toNNReal),ω)‖^2) μ:=hi0.add hi1
      have he:=ofReal_integral_eq_lintegral_ofReal hi
        (ae_of_all _ (fun _=>add_nonneg (sq_nonneg _) (sq_nonneg _)))
      have hadd:(∫ω,‖Left (zero_le_one.trans hL) k hL hρ.le ((v,s.toNNReal),ω)‖^2+
          ‖Right (zero_le_one.trans hL) k hL hρ.le ((v,s.toNNReal),ω)‖^2 ∂μ)=
          (∫ω,‖Left (zero_le_one.trans hL) k hL hρ.le ((v,s.toNNReal),ω)‖^2 ∂μ)+
          (∫ω,‖Right (zero_le_one.trans hL) k hL hρ.le ((v,s.toNNReal),ω)‖^2 ∂μ):=integral_add hi0 hi1
      exact he.symm.trans (congrArg ENNReal.ofReal hadd)
    _≤_:=ENNReal.ofReal_le_ofReal hcap


include haP htarget hstop hIJ₀ hIJ₁ hnull hJ hrootStop hrootTarget in
/-- The literal completed-window original-J output has its sharp
iterated past/sample mass before any common stochastic version is
selected. This is the mass required for the common version theorem. -/
theorem iterated(hA:P.coefficient=(fun z=>κ+aV z))
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
    (lam ε tail η:ℝ)(hlam:1≤lam)(htail:tail≤ε*(2*((p-1:ℕ):ℝ)))(hη:0<η)(hρη:ρ+η<1):
    (∫⁻v in Ioc (0:ℝ) ((H:ℝ)-(h:ℝ)),∫⁻ω,
      ENNReal.ofReal (‖Output hL hρ.le k v.toNNReal ω‖^2) ∂μ)≤
      ∫⁻v in Ioc (0:ℝ) ((H:ℝ)-(h:ℝ)),∫⁻s in Ioc (0:ℝ) (h:ℝ),ENNReal.ofReal
        (Env v.toNNReal h s.toNNReal k A0 ν Λ ρ χ lam ε tail η hL hρ hρhalf p Bcur Bword):=by
  apply lintegral_mono_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with v hv
  have hv':(v.toNNReal:ℝ)=v:=Real.coe_toNNReal _ hv.1.le
  have hvh:v.toNNReal+h≤H:=by
    apply NNReal.coe_le_coe.mp
    simpa only [NNReal.coe_add,hv'] using (show v+(h:ℝ)≤(H:ℝ) from by linarith [hv.2])
  exact energy 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
    P haP h Z htarget hstop F hF hFm J hIJ₀ hIJ₁ hnull hJ hAs hrootStop hrootTarget
    hA hlocal hL hρ hρhalf hpos v.toNNReal hvh hH k hsmall hsmallL2 hcenter
    hspan hspanF hspanC hspanS hHistory B1 hBDG1 A0 ν hA0 hν hjet
    p hp Bcur hBDGcur Bword hBDGword χ hχ hχ1 horder lam ε tail η hlam htail hη hρη

end SHE.MixedNativeHigherMovingCap
