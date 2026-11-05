module
public import SHE.MovingOrdinaryErrorEnergy
public import SHE.InitialRetainedTriangleEnergy
public import SHE.NativeOutputTimePatch
public import SHE.SectionEnergy
public import SHE.TimeMeasureMass
public import SHE.InitialOrdinaryErrorEnergy
public import SHE.InitialOrdinaryErrorOutput
public import SHE.NewestWindowBudget
public import SHE.InitialOrdinaryNewestActual
public import SHE.MixedOrdinaryErrorRootIdentity
public import SHE.MixedOrdinaryFiniteHilbertError
public import SHE.NativeBesselReparameter
public import SHE.NativeBesselFiniteSumEnergy
public import SHE.InitialOrdinaryNewestFibre
public import SHE.InitialOrdinaryNewestIntegration
public import SHE.RootSectionAverage
public import SHE.InitialOrdinaryNewestFields
public import SHE.InitialNativeKernelFibre
public import SHE.MixedNativePairInitial
public import SHE.MixedPastNewestOriginalMass
public import SHE.PhysicalWordErrorFields
public import SHE.MixedPastNewestOrdinaryError
public import SHE.InitialNativeKernelFields
public import SHE.InitialTerminalFields
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
namespace SHE.FullOrdinaryErrorOutput
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
attribute [local irreducible] GaussianConvolution.gaussianAverage ActualMeanKernel.cappedAverage
  GaussianTaylor.hessian WordRecursion.hessian UncutSmoothWords.test
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
local notation "L"=>InitialTerminalLevel.level R F hF hFm
local notation "Root"=>InitialTerminalLevel.Root R

local notation "Mean"=>InitialNativeKernelFields.mean 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h F hF hFm
local notation "Error"=>MixedPastNewestOrdinaryError.errorField 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S

local notation "BT" T:max=>InitialNativeKernelFibre.terminal Λ u₀ P haP h T
local notation "NB" T:max=>ControlledReferenceThetaGeometry.level P P.coefficient haP Λ 0 (BT T) bot_le
  (ControlledScalarReference.observations (BT T)) (fun _ _=>le_rfl) (fun _ _=>le_rfl) F hF hFm
local notation "K" T:max=>(NB T) (0,(embed u₀,0))
local notation "Lift" T:max=>InitialTerminalFields.lift R T
local notation "MA"=>InitialNativeKernelFibre.actualMean
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h F hF hFm
local notation "Point"=>InitialOrdinaryNewestFields.point
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h F hF hFm
local notation "CA" T:max=>MixedPastNewestOriginalMass.current
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP 0 (BT T) bot_le
  (ControlledScalarReference.observations (BT T)) (fun _ _=>le_rfl) (fun _ _=>le_rfl) F hF hFm
local notation "PA" T:max=>MixedPastNewestOriginalMass.primitive
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP 0 (BT T) bot_le
  (ControlledScalarReference.observations (BT T)) (fun _ _=>le_rfl) (fun _ _=>le_rfl) F hF hFm

local notation "Primitive"=>InitialOrdinaryNewestFields.primitive
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h F hF hFm

local notation "ZZ" T:max=>ControlledScalarReference.observations (BT T)
local notation "Average"=>InitialOrdinaryNewestFields.average
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h F hF hFm

variable (hL:1≤Λ){ρ:ℝ}(hρ:0≤ρ)
local notation "Value"=>InitialOrdinaryErrorOutput.value 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h F hF hFm hL hρ
local notation "TT" t:max=>(show Icc (R).base (R).horizon from InitialRetainedTriangleEnergy.clippedTime h (t:ℝ))
local notation "Moving"=>MovingOrdinaryErrorOutput.value
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h
  (ControlledScalarReference.observations h) (fun _ _=>le_rfl) (fun _ _=>le_rfl) F hF hFm hL hρ

def initial(depth:ℕ)(z:ℝ≥0×Ω):CircleL2:=
  if 0<z.1∧z.1≤h then Value depth (TT z.1,z.2) else 0
local notation "Initial"=>initial 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h F hF hFm hL hρ

theorem initial_measurable(depth:ℕ):Measurable (Initial depth):=by
  have hT:Measurable (fun t:ℝ≥0=>(TT t)):=
    (InitialRetainedTriangleEnergy.clippedTime_measurable h).comp NNReal.continuous_coe.measurable
  exact ((InitialOrdinaryErrorOutput.measurable
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h F hF hFm hL hρ depth).comp
      ((hT.comp measurable_fst).prodMk measurable_snd)).ite
        ((measurableSet_lt (α:=ℝ≥0) measurable_const measurable_fst).inter
          (measurableSet_le (α:=ℝ≥0) measurable_fst measurable_const)) measurable_const

def field(depth:ℕ):ℝ≥0×Ω→CircleL2:=NativeOutputTimePatch.field h (Initial depth) (Moving depth)
local notation "Field"=>field 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h F hF hFm hL hρ

theorem measurable(depth:ℕ):Measurable (Field depth):=
  NativeOutputTimePatch.measurable h _ _
    (initial_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h F hF hFm hL hρ depth)
    (MovingOrdinaryErrorOutput.measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h
      (ControlledScalarReference.observations h) (fun _ _=>le_rfl) (fun _ _=>le_rfl) F hF hFm hL hρ depth)

variable (J:StandardTerminalIto (C:=Both RealHaarInput) (E:=ℝ) 𝓕 μ H)
variable (hIJ₀:StandardScalarNaturality I₀ (leftIntegral 𝓕 μ H J))
variable (hIJ₁:StandardScalarNaturality I₁ (rightIntegral 𝓕 μ H J))
variable (hnull:NullCompleteFiltration.ContainsNullSets 𝓕 μ)(hJ:StandardFiniteIto.Universal 𝓕 μ H J)
variable (hAs:BoundedSmooth (fun z=>κ+aV z))
local notation "G" T:max=>MixedOrdinaryRootFields.error
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S J hIJ₀ hIJ₁ hnull hJ
  P hAs 0 0 (BT T) bot_le (ZZ T) (fun _=>rfl) (fun _=>rfl) F hF hFm
local notation "Disc" T:max=>MixedOrdinaryRootHilbertExpansion.discrepancy
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S J hIJ₀ hIJ₁ hnull hJ
  P hAs 0 0 (BT T) bot_le (ZZ T) (fun _=>rfl) (fun _=>rfl) F hF hFm hL hρ
variable (hsmall:ProfileStability.memoryConstant P.lower P.holder P.exponent*
  ProfileVolterra.powerConstant ((P.exponent-2)/4)*P.horizon^(P.exponent/4)≤1/2)

/-- The constant sample-energy cap transports to the literal native
output clock. Both endpoints of its original interval are retained. -/
private theorem clock_energy(T:ℝ≥0)(Y:ℝ≥0×Ω→CircleL2)(hY:Measurable Y)(C:ℝ)(hC:0≤C)
    (hs:∀t:ℝ≥0,0<t→t≤T→Integrable (fun ω=>‖Y (t,ω)‖^2) μ ∧
      (∫ω,‖Y (t,ω)‖^2 ∂μ)≤C):
    Integrable (fun z=>‖Y z‖^2) (energyMeasure μ T) ∧
      (∫z,‖Y z‖^2 ∂energyMeasure μ T)≤(T:ℝ)*C:=by
  have hm:Measurable (fun z=>ENNReal.ofReal (‖Y z‖^2)):=hY.norm.pow_const 2 |>.ennreal_ofReal
  have hcap:(∫⁻z,ENNReal.ofReal (‖Y z‖^2) ∂energyMeasure μ T)≤ENNReal.ofReal ((T:ℝ)*C):=by
    rw [energyMeasure,lintegral_prod _ hm.aemeasurable,timeMeasure_lintegral]
    calc
      _≤∫⁻t in Ioc (0:ℝ) (T:ℝ),ENNReal.ofReal C:=by
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
        have hn:0<t.toNNReal:=Real.toNNReal_pos.mpr ht.1
        have hl:t.toNNReal≤T:=(Real.toNNReal_le_iff_le_coe).mpr ht.2
        have hh:=hs t.toNNReal hn hl
        rw [←ofReal_integral_eq_lintegral_ofReal hh.1 (ae_of_all _ (fun _=>sq_nonneg _))]
        exact ENNReal.ofReal_le_ofReal hh.2
      _=ENNReal.ofReal ((T:ℝ)*C):=by
        rw [lintegral_const,Measure.restrict_apply MeasurableSet.univ,univ_inter,Real.volume_Ioc,sub_zero,←ENNReal.ofReal_mul hC]
        congr 1
        ring
  have hi:Integrable (fun z=>‖Y z‖^2) (energyMeasure μ T):=by
    refine ⟨(hY.norm.pow_const 2).aestronglyMeasurable,?_⟩
    rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ (fun _=>sq_nonneg _))]
    exact hcap.trans_lt ENNReal.ofReal_lt_top
  refine ⟨hi,?_⟩
  have he:=ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ (fun _=>sq_nonneg _))
  exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg T.2 hC)).mp (he.trans_le hcap)

include hsmall hIJ₀ hIJ₁ hnull hJ hAs in
/-- The literal full-time native ordinary finite approximation error,
including the initial triangle, has ONE numerical cap before smoothing. -/
theorem energy(hA:P.coefficient=(fun z=>κ+aV z))
    (D:SmoothApproximation.ScalarData){tau:ℝ}(htau:0<tau)(htau1:tau≤1)
    (hcontract:GaussianProfile.contractionConstant D.ell D.holderConstant D.beta*tau^(D.beta/4)≤1/2)
    (j:ℕ)(hP:P=ControlledSmoothLimit.smoothTotalParameters D htau htau1 hcontract j)
    (hU:aU=D.residualCoefficient)(hV:aV=D.smoothCoefficient j)
    {B Hr:ℝ}(hB:0≤B)(hHr:0≤Hr)
    (hroot:∀x z,|F x z|≤B)
    (hrootmod:∀x z w,|F x z-F x w|≤Hr*|z 0-w 0|^P.exponent)
    (hlocal:StandardTerminalPastLocality J)(hpos:0<h)(hhH:h≤H)(h1:(h:ℝ)≤1)
    (hspan:(h:ℝ)≤P.horizon)(depth:ℕ)
    (hold:∀i,i<depth→(h:ℝ)≤PhysicalScoreChain.uniformHorizon 1 i)
    (A0 ν:ℝ)(hA0:0≤A0)(hν:0≤ν)
    (hjet:∀x i,i≤depth→∀z,‖iteratedFDeriv ℝ i (F x) z‖≤A0*ν^i)
    (B0:ℕ→ℝ≥0)(hBDG:∀k,k<depth→StandardTerminalBDGPower (k+2) J (B0 k)):
    Integrable (fun z=>‖Field depth z‖^2) (energyMeasure μ H) ∧
      (∫z,‖Field depth z‖^2 ∂energyMeasure μ H)≤
        (H:ℝ)*(Λ^(-ρ)*(ScalarApproximationDiscrepancy.scalarError D j)^2*
          MixedPastNewestFiniteError.constant
            (ControlledSmoothLimit.roughTotalParameters D htau htau1 hcontract) κ M 0 1 B Hr depth B0 A0 ν):=by
  let Cap:ℝ:=Λ^(-ρ)*(ScalarApproximationDiscrepancy.scalarError D j)^2*
    MixedPastNewestFiniteError.constant
      (ControlledSmoothLimit.roughTotalParameters D htau htau1 hcontract) κ M 0 1 B Hr depth B0 A0 ν
  have hm(v:ℝ≥0)(hv:v+h≤H):Integrable (fun ω=>‖Moving depth (v,ω)‖^2) μ ∧
      (∫ω,‖Moving depth (v,ω)‖^2 ∂μ)≤Cap:=
    MovingOrdinaryErrorEnergy.section_energy
      𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h
      (ControlledScalarReference.observations h) (fun _ _=>le_rfl) (fun _ _=>le_rfl) F hF hFm
      hL hρ J hIJ₀ hIJ₁ hnull hJ hAs (fun _=>rfl) (fun _=>rfl) hsmall hA
      D htau htau1 hcontract j hP hU hV hB hHr hroot hrootmod hlocal hpos h1 (fun _=>rfl)
      hspan v hv depth hold A0 ν hA0 hν hjet B0 hBDG
  have hC:0≤Cap:=(integral_nonneg (fun ω=>sq_nonneg ‖Moving depth (0,ω)‖)).trans
    (hm 0 (by simpa only [zero_add] using hhH)).2
  have hme:Integrable (fun z=>‖Moving depth z‖^2) (energyMeasure μ (H-h)) ∧
      (∫z,‖Moving depth z‖^2 ∂energyMeasure μ (H-h))≤((H-h:ℝ≥0):ℝ)*Cap:=by
    apply clock_energy μ (H-h) (Moving depth)
      (MovingOrdinaryErrorOutput.measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h
        (ControlledScalarReference.observations h) (fun _ _=>le_rfl) (fun _ _=>le_rfl) F hF hFm hL hρ depth) Cap hC
    intro v _ hv
    apply hm v
    have hvr:(v:ℝ)≤(H:ℝ)-(h:ℝ):=by simpa only [NNReal.coe_sub hhH] using NNReal.coe_le_coe.mpr hv
    exact_mod_cast (show (v:ℝ)+(h:ℝ)≤(H:ℝ) by linarith)
  have hie:Integrable (fun z=>‖Initial depth z‖^2) (energyMeasure μ h) ∧
      (∫z,‖Initial depth z‖^2 ∂energyMeasure μ h)≤(h:ℝ)*Cap:=by
    apply clock_energy μ h (Initial depth)
      (initial_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h F hF hFm hL hρ depth) Cap hC
    intro t ht hth
    have hbteq:BT (TT t)=t:=by
      apply Subtype.ext
      change ClippedCovariance.clip 0 (h:ℝ) (t:ℝ)=(t:ℝ)
      exact ClippedCovariance.clip_eq ⟨t.2,by exact_mod_cast hth⟩
    have hi:=InitialOrdinaryErrorEnergy.section_energy
      𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h F hF hFm
      hL hρ J hIJ₀ hIJ₁ hnull hJ hAs hsmall hA
      D htau htau1 hcontract j hP hU hV hB hHr hroot hrootmod hlocal hhH h1
      hspan depth hold A0 ν hA0 hν hjet B0 hBDG (TT t) (by rw [hbteq];exact ht)
    have hit:0<t∧t≤h:=⟨ht,hth⟩
    simpa only [initial,ite_eq_left hit,Cap] using hi
  have he:=NativeOutputTimePatch.energy μ H h hhH (Initial depth) (Moving depth)
    (initial_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h F hF hFm hL hρ depth)
    (MovingOrdinaryErrorOutput.measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h
      (ControlledScalarReference.observations h) (fun _ _=>le_rfl) (fun _ _=>le_rfl) F hF hFm hL hρ depth)
    hie.1 hme.1
  refine ⟨he.1,?_⟩
  change (∫z,‖NativeOutputTimePatch.field h (Initial depth) (Moving depth) z‖^2 ∂energyMeasure μ H)≤(H:ℝ)*Cap
  rw [he.2]
  have hc:=add_le_add hie.2 hme.2
  rw [NNReal.coe_sub hhH] at hc
  nlinarith

/-- The original completed-window discrepancy sum in the actual
paired finite Hilbert expansion. -/
def movingOriginal(depth:ℕ)(z:ℝ≥0×Ω):CircleL2:=
  ∑k∈Finset.range depth,MixedOrdinaryRootHilbertExpansion.discrepancy
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S J hIJ₀ hIJ₁ hnull hJ P hAs 0
    z.1 (z.1+h) le_self_add
    (ObservationFamilyTimeShift.family (z.1:ℝ) (ControlledScalarReference.observations h))
    (MixedNativeHigherMovingEnergy.rootStop h (ControlledScalarReference.observations h) (fun _=>rfl) z.1)
    (MixedNativeHigherMovingEnergy.rootTarget h (ControlledScalarReference.observations h) (fun _=>rfl) z.1)
    F hF hFm hL hρ k z.2
local notation "MO"=>movingOriginal 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
  P h F hF hFm hL hρ J hIJ₀ hIJ₁ hnull hJ hAs

/-- The original initial-window discrepancy sum, kept on its actual
variable terminal rather than continued as a completed window. -/
def initialOriginal(depth:ℕ)(z:ℝ≥0×Ω):CircleL2:=
  if 0<z.1∧z.1≤h then ∑k∈Finset.range depth,(Disc (TT z.1)) k z.2 else 0
local notation "IO"=>initialOriginal 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
  P haP h F hF hFm hL hρ J hIJ₀ hIJ₁ hnull hJ hAs

def original(depth:ℕ):ℝ≥0×Ω→CircleL2:=NativeOutputTimePatch.field h (IO depth) (MO depth)
local notation "Original"=>original 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
  P haP h F hF hFm hL hρ J hIJ₀ hIJ₁ hnull hJ hAs

include hsmall in
/-- ONE original initial sample event identifies the full Borel native
error with the exact paired-expansion discrepancy, at EVERY output time. -/
theorem identified_all_times_ae(hA:P.coefficient=(fun z=>κ+aV z)):
    ∀ᵐω∂μ,∀t:ℝ≥0,∀depth:ℕ,Field depth (t,ω)=Original depth (t,ω):=by
  filter_upwards [InitialOrdinaryErrorOutput.value_all_parameters_ae
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h F hF hFm
    hL hρ J hIJ₀ hIJ₁ hnull hJ hAs hsmall hA] with ω hω
  intro t depth
  change NativeOutputTimePatch.field h (Initial depth) (Moving depth) (t,ω)=
    NativeOutputTimePatch.field h (IO depth) (MO depth) (t,ω)
  unfold NativeOutputTimePatch.field
  dsimp only [Prod.fst,Prod.snd]
  by_cases hth:t≤h
  · simp only [ite_eq_left hth,initial,initialOriginal]
    by_cases ht:0<t∧t≤h
    · simp only [ite_eq_left ht]
      exact hω (TT t) depth
    · simp only [ite_eq_right ht]
  · simp only [ite_eq_right hth]
    exact MovingOrdinaryErrorOutput.value_eq
      𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h
      (ControlledScalarReference.observations h) (fun _ _=>le_rfl) (fun _ _=>le_rfl) F hF hFm
      hL hρ J hIJ₀ hIJ₁ hnull hJ hAs (fun _=>rfl) (fun _=>rfl) hsmall hA (t-h) depth ω

end SHE.FullOrdinaryErrorOutput
