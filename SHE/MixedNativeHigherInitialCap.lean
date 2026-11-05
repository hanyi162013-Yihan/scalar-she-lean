module
public import SHE.MixedNativeHigherInitialEnergy
public import SHE.InitialNativeColumnEnergy
public import SHE.MovingNativeFourTermEnergy
public import SHE.InitialRetainedTriangleEnergy

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2500000
set_option quotPrecheck false
namespace SHE.MixedNativeHigherInitialCap
open MeasureTheory PredictableL2 NativeHeatObservation NativeObservationNaturality
open FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation StoppedItoInputs
open scoped NNReal ENNReal
local instance mixedNativeHigherInitialCap_realSigma : MeasurableSpace RealL2 := borel _
local instance mixedNativeHigherInitialCap_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance mixedNativeHigherInitialCap_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance mixedNativeHigherInitialCap_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance mixedNativeHigherInitialCap_blockSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance mixedNativeHigherInitialCap_blockBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
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


local instance mixedNativeHigherInitialCap_circleSigma : MeasurableSpace CircleL2 := borel _
local instance mixedNativeHigherInitialCap_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩



open Real AddCircle Set Filter WordRecursion ControlledProfile ControlledReferenceLevel SmoothCylinders UniformSmooth
  CutoffWordLevel CutoffWordHistories CutoffCarriers PhysicalScoreChain PhysicalChainArrays
  PhysicalParentGeometry CoveredHistoryGeometry CoveredControlledLaw ControlledOldIntervals
  ControlledFamilyProfileForest GaussianIncrement GaussianConvolution MeasurableGaussianScores
open ProfileStability ProfileL2
open HistoryProductMeasure
open scoped BigOperators
local instance mixedNativeHigherInitialCap_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
local instance mixedNativeHigherInitialCap_nativeSecond:SecondCountableTopology CircleL2:=
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
local instance mixedNativeHigherInitialCap_spaceSigma:MeasurableSpace NativeKernelHaarColumns.Space:=borel _
local instance mixedNativeHigherInitialCap_spaceBorel:BorelSpace NativeKernelHaarColumns.Space:=⟨rfl⟩


local notation "Output"=>MixedNativeHigherInitialEnergy.output 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
  P haP h F hF hFm J hIJ₀ hIJ₁ hnull hJ hAs
local notation "Env"=>MovingNativeFourTermEnergy.envelope 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P

include hIJ₀ hIJ₁ hnull hJ in
/-- The actual initial original-J output obeys the same complete cap,
including its variable root terminal and true common initial state. -/
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
    (∫⁻ω,ENNReal.ofReal (‖Output hL hρ.le k T ω‖^2) ∂μ)≤
      ∫⁻q in Ioc (0:ℝ) ((BT T):ℝ),ENNReal.ofReal
        (Env 0 (BT T) q.toNNReal k A0 ν Λ ρ χ lam ε tail η hL hρ hρhalf p Bcur Bword):=by
  rw [MixedNativeHigherInitialEnergy.energy
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h F hF hFm
    J hIJ₀ hIJ₁ hnull hJ hAs hA hlocal hL hρ hρhalf hhH hH k T hT
    hsmall hsmallL2 hspan hspanF hspanC hspanS hHistory B1 hBDG1 A0 ν hA0 hν hjet
    p hp Bcur hBDGcur Bword hBDGword χ hχ hχ1 horder lam ε tail η hlam htail hη hρη]
  rw [←restrict_Ioo_eq_restrict_Ioc]
  apply lintegral_mono_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with q hq
  have hq0:0<q.toNNReal:=Real.toNNReal_pos.mpr hq.1
  have hqt:q.toNNReal<BT T:=by
    apply NNReal.coe_lt_coe.mp
    simpa only [Real.coe_toNNReal _ hq.1.le] using hq.2
  obtain ⟨hi0,hi1,hcap⟩:=InitialNativeColumnEnergy.energy
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
    P haP h F hF hFm J hIJ₀ hIJ₁ k (zero_lt_one.trans_le hL) hlocal hsmall hsmallL2
    hspan hspanF hspanC hspanS hHistory
    T q.toNNReal hq0 hqt hhH hH B1 hBDG1 A0 ν hA0 hν hjet
    p hp Bcur hBDGcur Bword hBDGword χ hχ hχ1 horder
    Λ ρ lam ε tail η hL hρ hρhalf hlam htail hη hρη
  have hT1:((BT T):ℝ)≤1:=le_trans (by exact_mod_cast (T.2.2.trans hhH)) hH
  have hbudget:=MovingNativeFourTermEnergy.budget_le
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P
    0 (BT T) q.toNNReal hq0 hqt hT1 k A0 ν Λ ρ χ lam ε tail η hL hρ hρhalf hlam p Bcur Bword
  simp only [zero_add] at hbudget
  have hfinal:=hcap.trans hbudget
  calc
    _=ENNReal.ofReal ((∫ω,‖Left (zero_le_one.trans hL) k hL hρ.le ((T,q.toNNReal),ω)‖^2 ∂μ)+
        (∫ω,‖Right (zero_le_one.trans hL) k hL hρ.le ((T,q.toNNReal),ω)‖^2 ∂μ)):=by
      have hi:Integrable (fun ω=>‖Left (zero_le_one.trans hL) k hL hρ.le ((T,q.toNNReal),ω)‖^2+
          ‖Right (zero_le_one.trans hL) k hL hρ.le ((T,q.toNNReal),ω)‖^2) μ:=hi0.add hi1
      have he:=ofReal_integral_eq_lintegral_ofReal hi
        (ae_of_all _ (fun _=>add_nonneg (sq_nonneg _) (sq_nonneg _)))
      have hadd:(∫ω,‖Left (zero_le_one.trans hL) k hL hρ.le ((T,q.toNNReal),ω)‖^2+
          ‖Right (zero_le_one.trans hL) k hL hρ.le ((T,q.toNNReal),ω)‖^2 ∂μ)=
          (∫ω,‖Left (zero_le_one.trans hL) k hL hρ.le ((T,q.toNNReal),ω)‖^2 ∂μ)+
          (∫ω,‖Right (zero_le_one.trans hL) k hL hρ.le ((T,q.toNNReal),ω)‖^2 ∂μ):=integral_add hi0 hi1
      exact he.symm.trans (congrArg ENNReal.ofReal hadd)
    _≤_:=ENNReal.ofReal_le_ofReal hfinal


/-- The literal initial original-J output on the real terminal clock.
No joint stochastic version is asserted by this definition. -/
def realOutput(hL:1≤Λ){ρ:ℝ}(hρ:0≤ρ)(k:ℕ)(t:ℝ)(ω:Ω):CircleL2:=
  Output hL hρ k (InitialRetainedTriangleEnergy.clippedTime h t) ω
local notation "RealOutput"=>realOutput 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
  P haP h F hF hFm J hIJ₀ hIJ₁ hnull hJ hAs

include hIJ₀ hIJ₁ hnull hJ in
/-- The entire literal initial strip has an iterated past/sample cap,
with the physical terminal T retained before stochastic versions are
chosen. The actual initial-past energy vanishes in its clock ledger. -/
theorem iterated(hA:P.coefficient=(fun z=>κ+aV z))
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
    (lam ε tail η:ℝ)(hlam:1≤lam)(htail:tail≤ε*(2*((p-1:ℕ):ℝ)))(hη:0<η)(hρη:ρ+η<1):
    (∫⁻t in Ioc (0:ℝ) (min (H:ℝ) (h:ℝ)),∫⁻ω,
      ENNReal.ofReal (‖RealOutput hL hρ.le k t ω‖^2) ∂μ)≤
      ∫⁻t in Ioc (0:ℝ) (min (H:ℝ) (h:ℝ)),∫⁻q in Ioc (0:ℝ) t,ENNReal.ofReal
        (Env 0 t.toNNReal q.toNNReal k A0 ν Λ ρ χ lam ε tail η hL hρ hρhalf p Bcur Bword):=by
  apply lintegral_mono_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  let T:Icc (R).base (R).horizon:=InitialRetainedTriangleEnergy.clippedTime h t
  have hclip:(T:ℝ)=t:=ClippedCovariance.clip_eq ⟨ht.1.le,ht.2.trans (min_le_right _ _)⟩
  have hT:0<BT T:=by
    change (0:ℝ)<(T:ℝ)
    rw [hclip]
    exact ht.1
  have hterminal:BT T=t.toNNReal:=by
    ext
    change (T:ℝ)=(t.toNNReal:ℝ)
    rw [hclip,Real.coe_toNNReal _ ht.1.le]
  have hh:=energy 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
    P haP h F hF hFm J hIJ₀ hIJ₁ hnull hJ hAs hA hlocal hL hρ hρhalf
    hhH hH k T hT hsmall hsmallL2 hspan hspanF hspanC hspanS hHistory
    B1 hBDG1 A0 ν hA0 hν hjet p hp Bcur hBDGcur Bword hBDGword χ hχ hχ1 horder
    lam ε tail η hlam htail hη hρη
  simpa only [realOutput,hterminal,Real.coe_toNNReal _ ht.1.le] using hh

end SHE.MixedNativeHigherInitialCap
