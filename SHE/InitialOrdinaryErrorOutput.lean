module
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
namespace SHE.InitialOrdinaryErrorOutput
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

def scalar(depth:ℕ)(z:((Icc (R).base (R).horizon)×Ω)×HeatCircle):ℂ:=
  ∑k∈Finset.range depth,(Average k z:ℂ)
local notation "Scalar"=>scalar 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h F hF hFm

theorem scalar_measurable(depth:ℕ):Measurable (Scalar depth):=
  Finset.measurable_sum _ (fun k _=>Complex.continuous_ofReal.measurable.comp
    (InitialOrdinaryNewestFields.average_measurable
      𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h F hF hFm k))

variable (hL:1≤Λ){ρ:ℝ}(hρ:0≤ρ)
def value(depth:ℕ):((Icc (R).base (R).horizon)×Ω)→CircleL2:=
  NativeBesselFieldAE.value Λ ρ hL hρ (Scalar depth)
local notation "Value"=>value 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h F hF hFm hL hρ

theorem measurable(depth:ℕ):Measurable (Value depth):=
  NativeBesselFieldAE.measurable Λ ρ hL hρ _ (scalar_measurable
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h F hF hFm depth)

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

include hsmall hL in
/-- ONE original initial sample event is selected before every terminal
and every finite discrepancy sum. -/
theorem scalar_all_parameters_ae(hA:P.coefficient=(fun z=>κ+aV z)):
    ∀ᵐω∂μ,∀T:Icc (R).base (R).horizon,∀depth:ℕ,∀x:HeatCircle,
      Scalar depth ((T,ω),x)=∑k∈Finset.range depth,((G T) k (ω,x):ℂ):=by
  filter_upwards [InitialOrdinaryNewestActual.average_all_parameters_ae
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h F hF hFm] with ω hω
  intro T depth x
  unfold scalar
  apply Finset.sum_congr rfl
  intro k _
  congr 1
  have he:=MixedOrdinaryErrorRootIdentity.error_eq_average
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S J hIJ₀ hIJ₁ hnull hJ
    P haP hAs 0 (BT T) bot_le (ZZ T) (fun _=>rfl) (fun _=>rfl) F hF hFm hsmall hA (zero_le_one.trans hL) k ω x
  have hages:=MixedOrdinaryErrorPrimitive.ages (BT T) (ZZ T) (fun _=>rfl) (fun _=>rfl)
  have hp:=MixedPastNewestOrdinaryError.primitive_eq_error
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP 0 (BT T) bot_le
    (ZZ T) (fun _ _=>le_rfl) (fun _ _=>le_rfl) F hF hFm hages k
  have hfun:MixedPastNewestOrdinaryError.primitive
      𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP 0 (BT T) bot_le
      (ZZ T) (fun _ _=>le_rfl) (fun _ _=>le_rfl) F hF hFm k=(PA T) k Error:=funext hp
  rw [hfun] at he
  exact (he.trans (hω T k x)).symm

include hsmall in
/-- The initial Borel native field is the actual finite ordinary
Hilbert discrepancy on the same event for ALL output times. -/
theorem value_all_parameters_ae(hA:P.coefficient=(fun z=>κ+aV z)):
    ∀ᵐω∂μ,∀T:Icc (R).base (R).horizon,∀depth:ℕ,
      Value depth (T,ω)=∑k∈Finset.range depth,(Disc T) k ω:=by
  filter_upwards [scalar_all_parameters_ae
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h F hF hFm
    hL J hIJ₀ hIJ₁ hnull hJ hAs hsmall hA] with ω hω
  intro T depth
  let Gc:ℕ→Ω×HeatCircle→ℂ:=fun k z=>((G T) k z:ℂ)
  have hG(k:ℕ):Measurable (Gc k):=Complex.continuous_ofReal.measurable.comp
    (MixedOrdinaryRootHilbertExpansion.error_measurable
      𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S J hIJ₀ hIJ₁ hnull hJ
      P hAs 0 0 (BT T) bot_le (ZZ T) (fun _=>rfl) (fun _=>rfl) F hF hFm hsmall hL k)
  have hp(k:ℕ):MemLp (fun x=>Gc k (ω,x)) 2 haarAddCircle:=
    MixedOrdinaryRootHilbertExpansion.error_section_memLp
      𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S J hIJ₀ hIJ₁ hnull hJ
      P hAs 0 0 (BT T) bot_le (ZZ T) (fun _=>rfl) (fun _=>rfl) F hF hFm hsmall hL k ω
  have hsum:MemLp (fun x=>Scalar depth ((T,ω),x)) 2 haarAddCircle:=by
    rw [show (fun x=>Scalar depth ((T,ω),x))=(fun x=>∑k∈Finset.range depth,Gc k (ω,x)) from
      funext (fun x=>hω T depth x)]
    exact memLp_finsetSum _ (fun k _=>hp k)
  let Q:Ω×HeatCircle→ℂ:=fun z=>∑k∈Finset.range depth,Gc k z
  have hQ:Measurable Q:=Finset.measurable_sum _ (fun k _=>hG k)
  have hqp:MemLp (fun x=>Q (ω,x)) 2 haarAddCircle:=memLp_finsetSum _ (fun k _=>hp k)
  have hsm:=scalar_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h F hF hFm depth
  have hl:=MeasurableL2FieldAE.realization_ae haarAddCircle (Scalar depth) hsm
    (T,ω) ((MeasurableL2FieldAE.section_memLp_iff haarAddCircle (Scalar depth) hsm (T,ω)).mp hsum)
  have hr:=MeasurableL2FieldAE.realization_ae haarAddCircle Q hQ ω
    ((MeasurableL2FieldAE.section_memLp_iff haarAddCircle Q hQ ω).mp hqp)
  have hreal:MeasurableL2FieldAE.realization haarAddCircle (Scalar depth) (T,ω)=
      MeasurableL2FieldAE.realization haarAddCircle Q ω:=by
    apply Lp.ext
    exact (hl.trans (ae_of_all _ (fun x=>hω T depth x))).trans hr.symm
  change OneInputOperator.besselHalf Λ ρ hL hρ
    (MeasurableL2FieldAE.realization haarAddCircle (Scalar depth) (T,ω))=_
  rw [hreal]
  change NativeBesselFieldAE.value Λ ρ hL hρ Q ω=_
  rw [NativeBesselFiniteSumEnergy.value Λ ρ hL hρ (Finset.range depth) Gc hG ω (fun k _=>hp k)]
  rfl
end SHE.InitialOrdinaryErrorOutput
