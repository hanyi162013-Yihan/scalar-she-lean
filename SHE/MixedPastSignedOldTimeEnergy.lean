module
public import SHE.MixedPastSignedEndpointRMS
public import SHE.MixedPastSignedEndpointFields
public import SHE.PastSignedEndpointBudget
public import SHE.HilbertFiniteAverage
public import SHE.MixedPastSignedEndpointTrace
public import SHE.RawTraceRMS
public import SHE.MixedPastKernelSections
public import SHE.RelativeKernelTruncationZero
public import SHE.ControlledFamilyKernelBounds

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2600000
set_option quotPrecheck false

namespace SHE.MixedPastSignedOldTimeEnergy
open MeasureTheory PredictableL2 NativeHeatObservation NativeObservationNaturality
open FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation StoppedItoInputs
open scoped NNReal ENNReal
local instance mixedPastSignedEndpointMoments_realSigma : MeasurableSpace RealL2 := borel _
local instance mixedPastSignedEndpointMoments_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance mixedPastSignedEndpointMoments_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance mixedPastSignedEndpointMoments_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance mixedPastSignedEndpointMoments_blockSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance mixedPastSignedEndpointMoments_blockBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
local instance : MeasurableSpace CircleHeat.CircleL2:=borel _
local instance : BorelSpace CircleHeat.CircleL2:=⟨rfl⟩
variable {Ω : Type} [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
variable (Λ κ : ℝ) (hκ : 0<κ) {aU aV : ℝ→ℝ} (haU : Measurable aU) (haV : Measurable aV) {ell M : ℝ}
variable (hell : 0<ell) (hbU : ∀ z,ell≤aU z ∧ aU z≤M) (hbV : ∀ z,ell≤aV z ∧ aV z≤M)
variable (I₀ I₁ : StandardTerminalIto (C := RealHaarIntegrand.Columns) (E := RealL2) 𝓕 μ H)
variable (u₀ : RealL2)
variable (S : MixedNativeAdditiveResidualPair.Solution 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀)
variable (J : StandardTerminalIto (C := Both RealHaarInput) (E := ℝ) 𝓕 μ H)
variable (hIJ₀ : StandardScalarNaturality I₀ (leftIntegral 𝓕 μ H J))
variable (hIJ₁ : StandardScalarNaturality I₁ (rightIntegral 𝓕 μ H J))

open PastItoInputs PastItoAlgebra PhysicalProfile


local instance mixedPastSignedEndpointMoments_circleSigma : MeasurableSpace CircleL2 := borel _
local instance mixedPastSignedEndpointMoments_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩



open Real AddCircle Set Filter WordRecursion ControlledProfile ControlledReferenceLevel SmoothCylinders UniformSmooth
  CutoffWordLevel CutoffWordHistories CutoffCarriers PhysicalScoreChain PhysicalChainArrays
  PhysicalParentGeometry CoveredHistoryGeometry CoveredControlledLaw ControlledOldIntervals
  ControlledFamilyProfileForest GaussianIncrement GaussianConvolution MeasurableGaussianScores
open ProfileStability ProfileL2
open HistoryProductMeasure
open scoped BigOperators
local instance mixedPastSignedEndpointMoments_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
variable (P : CanonicalCovariance.ProfileParameters) (haP : BoundedSmooth P.coefficient)
variable (v b : ℝ≥0) (hvb : v ≤ b)
variable (Z : VariableObservations.Family HeatCircle 1)
variable (htarget : ∀ x i,(b:ℝ) ≤ (Z.observations x i).target)
variable (hstop : ∀ x i,(b:ℝ) ≤ (Z.observations x i).stop)
variable (F : HeatCircle→WordRecursion.State 1→ℝ) (hF : UniformBoundedSmooth F)
variable (hFm : Measurable (fun z : HeatCircle×WordRecursion.State 1=>F z.1 z.2))
local notation "Base" => ControlledReferenceThetaGeometry.level P P.coefficient haP Λ v b hvb Z htarget hstop F hF hFm
local notation "Zero" => Base (0,(0,0))
local notation "U" => MixedPastJointData.pastU 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S v
local notation "Dir" => MixedPastJointData.pastD 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S v

local notation "Field"=>MixedPastNativeKernel.field
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP v b hvb Z htarget hstop F hF hFm
local notation "Frame"=>MixedPastNativeKernelTrace.frame Λ P haP v b hvb Z htarget hstop F hF hFm

local notation "Current"=>MixedPastNativeKernelEnergy.current
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP v b hvb Z htarget hstop F hF hFm
local notation "RowVariance"=>MixedPastNativeKernelEnergy.rowVariance Λ P haP v b hvb Z htarget hstop F hF hFm
local notation "RowResidual"=>MixedPastNativeKernelEnergy.rowResidual
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP v b hvb Z htarget hstop F hF hFm

local notation "AAmp"=>MixedPastNativeAAmplitude.amplitude
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP v b hvb Z htarget hstop F hF hFm


local notation "Spatial"=>MixedPastNativeKernelAverage.spatial
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP v b hvb Z htarget hstop F hF hFm
local notation "PastEnergy"=>MixedPastNativeKernelActual.pastEnergy
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP v b hvb Z htarget hstop F hF hFm
local notation "CurrentEnergy"=>MixedPastNativeKernelActual.currentEnergy
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP v b hvb Z htarget hstop F hF hFm
attribute [local irreducible] MixedPastNativeKernel.field MixedPastNativeKernelAverage.spatial
  MixedPastNativeKernelActual.pastEnergy MixedPastNativeKernelActual.currentEnergy MixedPastWordMoments.total

open ActualMeanKernel NativeRandomKernel NormalizedKernelSplit NativeSignedHaarProcess SignedKernelTruncation
local notation "Endpoint"=>MixedPastKernelFields.spatial
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S P haP v b hvb Z htarget hstop F hF hFm
local notation "CU"=>ContinuousHeatMild.coefficientFunction haU hell hbU S.first
local notation "CV"=>ContinuousHeatMild.coefficientFunction haV hell hbV S.second

local instance mixedPastSignedOldTimeEnergy_nativeSecond:SecondCountableTopology CircleL2:=
  (_root_.fourierBasis (T:=2*Real.pi)).repr.toHomeomorph.secondCountableTopology
local instance mixedPastSignedOldTimeEnergy_spaceSigma:MeasurableSpace SignedKernelColumns.Space:=borel _
local instance mixedPastSignedOldTimeEnergy_spaceBorel:BorelSpace SignedKernelColumns.Space:=⟨rfl⟩

include hIJ₀ hIJ₁ in
/-- Actual signed endpoint columns are averaged over ORIGINAL old times
before their square. The original current negative-input energy and the
arbitrary bad-tail power survive this genuine Hilbert Minkowski step. -/
theorem energy (hlocal:StandardTerminalPastLocality J)(hΛ:0≤Λ)
    (hages:∀x i,(Z.observations x i).stop≤(Z.observations x i).target)
    (hrootStop:∀x i,(Z.observations x i).stop≤(b:ℝ))
    (hrootTarget:∀x i,(Z.observations x i).target=(b:ℝ))
    (hcenter:∀x,(Z.observations x 0).center=x)(hspan:(b:ℝ)-(v:ℝ)≤P.horizon)
    (k:ℕ)(hfresh:(b:ℝ)-(v:ℝ)≤UniformFutureProfileScores.horizon (1+k))
    (hold:∀j,j<k→(b:ℝ)-(v:ℝ)≤uniformHorizon 1 j)
    (A0 ν:ℝ)(hA0:0≤A0)(hν:0≤ν)
    (hjet:∀x j,j≤k→∀z,‖iteratedFDeriv ℝ j (F x) z‖≤A0*ν^j)
    (order:ℕ)(B0:ℝ≥0)(hBDG:StandardTerminalBDGPower ((order+1)*(k+2)) J B0)
    (q:ℝ≥0)(hvq:v≤q)(hqb:q<b)(hqH:q≤H)(hwidth1:(b:ℝ)-(q:ℝ)≤1)
    (mass ρ lam ε tail η:ℝ)(hmass:1≤mass)(hρ:0<ρ)(hρhalf:ρ<1/2)
    (hlam:1≤lam)(htail:tail≤ε*(2*order))(hη:0<η)(hρη:ρ+η<1):
    let Jt:=MixedPastSignedEndpointMoments.traceConstant (Ω:=Ω) (M:=M) hell ρ hρ hρhalf
    let C:=MixedPastWordMoments.momentConstant P k k (order+1)
      ((k:ℝ)*(NativeHybridMoments.momentConstant ((order+1)*(k+2)) B0 κ M)^P.exponent)
    let E:=∫ω,inputEnergy hmass hρ.le (CU (q,ω)) (CV (q,ω)) ∂μ
    let old:=Measure.pi (fun _:Fin k=>volume.restrict (Ioc (v:ℝ) (b:ℝ)))
    let raw:=MixedPastSignedEndpointFields.raw
      𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP v b hvb Z htarget hstop F hF hFm k q hmass hρ.le
    Integrable raw (old.prod μ) ∧ Integrable (fun ω=>‖∫t,raw (t,ω) ∂old‖^2) μ ∧
      (∫ω,‖∫t,raw (t,ω) ∂old‖^2 ∂μ)≤
        (PastSignedEndpointTime.goodCoefficient P k Jt ρ η*lam^ε*((b:ℝ)-(q:ℝ))^((ρ+η)/2)*sqrt E*
          QuarterRMSTimeFactors.oldTimeBudget P (fraction P*P.lower) (uniformConstant 1)
            k ((b:ℝ)-(v:ℝ)) ((q:ℝ)-(v:ℝ)) (RawTraceTimeEnvelope.freshDegree ρ η) A0 ν+
        PastSignedEndpointTime.badCoefficient P k M C*lam^(-tail/2)*
          QuarterRMSTimeFactors.oldTimeBudget P (fraction P*P.lower) (uniformConstant 1)
            k ((b:ℝ)-(v:ℝ)) ((q:ℝ)-(v:ℝ)) (1/2:ℝ) A0 ν)^2:=by
  intro Jt C E old raw
  let A:=PastSignedEndpointTime.value Zero P (b:ℝ) k Λ q A0 ν Jt ρ η lam ε M C tail E
  have hA:=PastSignedEndpointTime.value_measurable Zero P (b:ℝ) k Λ q A0 ν Jt ρ η lam ε M C tail E
  have hAn:=PastSignedEndpointTime.value_nonneg Zero P (b:ℝ) (fun _=>rfl)
    k Λ q A0 ν Jt ρ η lam ε M C tail E (zero_lt_one.trans_le hlam).le
  have hbudget:=PastSignedEndpointTime.old_time_bound Zero P (b:ℝ) (fun _=>rfl)
    k Λ q A0 ν Jt ρ η lam ε M C tail E hΛ hρ.le hη.le hρη (zero_lt_one.trans_le hlam).le
    (by exact_mod_cast hvq) (by exact_mod_cast hqb) (by rfl) hA0 hν
  have hraw:=MixedPastSignedEndpointFields.raw_measurable
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP v b hvb Z htarget hstop F hF hFm
    hΛ k q hmass hρ.le
  have hs:=MixedPastSignedEndpointRMS.energy
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S J hIJ₀ hIJ₁ P haP v b hvb Z htarget hstop F hF hFm
    hlocal hΛ hages hrootStop hrootTarget hcenter hspan k hfresh hold A0 ν hA0 hν hjet
    order B0 hBDG q hvq hqH hwidth1 mass ρ lam ε tail η hmass hρ hρhalf hlam htail hη
  have hsection:∀ᵐt∂old,Integrable (fun ω=>‖raw (t,ω)‖^2) μ ∧
      (∫ω,‖raw (t,ω)‖^2 ∂μ)≤A t^2:=by
    filter_upwards [hs] with t ht
    by_cases ha:QuarterSpatialEvent.active Zero (b:ℝ) k q t
    · have hh:=ht ha
      have heq: (fun ω=>raw (t,ω))=fun ω=>SignedKernelColumns.rawColumns (Endpoint k 1 q q t)
          mass ρ hmass hρ.le ell M hell (fun ω=>CU (q,ω)) (fun ω=>CV (q,ω)) ω:=
        funext (fun ω=>MixedPastSignedEndpointFields.raw_section
          𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP v b hvb Z htarget hstop F hF hFm
          k q hmass hρ.le t ω)
      simp_rw [show ∀ω,raw (t,ω)=SignedKernelColumns.rawColumns (Endpoint k 1 q q t)
        mass ρ hmass hρ.le ell M hell (fun ω=>CU (q,ω)) (fun ω=>CV (q,ω)) ω
          from fun ω=>congrFun heq ω]
      simpa only [A,PastSignedEndpointTime.value,if_pos ha] using hh
    · have hz(ω):raw (t,ω)=0:=MixedPastSignedEndpointFields.raw_zero
        𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP v b hvb Z htarget hstop F hF hFm
        k q t hvq ha hmass hρ.le ω
      simp only [hz,norm_zero,zero_pow (by norm_num:(2:ℕ)≠0),integral_zero]
      exact ⟨integrable_const _,sq_nonneg _⟩
  have hh:=HilbertParameterAverage.finite_energy μ old raw hraw A hA hbudget.1 hAn
    (hsection.mono (fun _ h=>h.1)) (hsection.mono (fun _ h=>h.2))
  refine ⟨hh.1,hh.2.1,hh.2.2.trans ?_⟩
  exact pow_le_pow_left₀ (integral_nonneg hAn) hbudget.2 2

end SHE.MixedPastSignedOldTimeEnergy
