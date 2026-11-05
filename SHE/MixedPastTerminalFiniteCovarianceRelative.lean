module

public import SHE.ControlledFiniteCovarianceRelative
public import SHE.MixedPastTerminalFiniteCovariance
public import SHE.MixedPastTerminalPairedIdentity
public import SHE.MixedPastTerminalPairedFields
public import SHE.JointHistoryFields
public import SHE.WeightedRowTimeShift
public import SHE.ControlledThetaRelativeArrays
public import SHE.ControlledThetaWeightedFields
public import SHE.MixedPastDecayedWord
public import SHE.RelativeHistoryGeometry
public import SHE.ParentHeatFields
public import SHE.MixedPastActualMean
public import SHE.MixedPastJointData
public import SHE.MixedNativeJointHistory
public import SHE.ControlledJointMeanIdentity
public import SHE.CarrierStopBounds
public import SHE.CoveredControlledLaw
public import SHE.JointWordAnalytic
public import SHE.PastEventWeights
public import SHE.VaryingControlledGaussianFields
public import SHE.MixedNativePastWeightedMoments
public import SHE.MixedNativePastThetaMoments
public import SHE.NativePastHybridMoments
public import SHE.ControlledProfile
public import SHE.PastHybridIntegral
public import SHE.PastItoAlgebra
public import SHE.MixedNativePairObservation
public import SHE.NativePairScaledMartingale
public import SHE.NativePairLocalMartingale
public import SHE.NativePairExtendedMartingale

@[expose] public section
noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000

namespace SHE.MixedPastTerminalFiniteCovarianceRelative
open MeasureTheory PredictableL2 NativeHeatObservation NativeObservationNaturality
open FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation StoppedItoInputs
open scoped NNReal ENNReal
local instance mixedPastLiteralPoint_realSigma : MeasurableSpace RealL2 := borel _
local instance mixedPastLiteralPoint_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance mixedPastLiteralPoint_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance mixedPastLiteralPoint_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance mixedPastLiteralPoint_blockSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance mixedPastLiteralPoint_blockBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
variable {Ω : Type} [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
variable (Λ κ : ℝ) (hκ : 0<κ) {aU aV : ℝ→ℝ} (haU : Measurable aU) (haV : Measurable aV) {ell M : ℝ}
variable (hell : 0<ell) (hbU : ∀ z,ell≤aU z ∧ aU z≤M) (hbV : ∀ z,ell≤aV z ∧ aV z≤M)
variable (I₀ I₁ : StandardTerminalIto (C := RealHaarIntegrand.Columns) (E := RealL2) 𝓕 μ H)
variable (u₀ v₀ : RealL2)
variable (S : MixedNativeAdditiveResidualPair.Solution 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀)
variable (J : StandardTerminalIto (C := Both RealHaarInput) (E := ℝ) 𝓕 μ H)
variable (hIJ₀ : StandardScalarNaturality I₀ (leftIntegral 𝓕 μ H J))
variable (hIJ₁ : StandardScalarNaturality I₁ (rightIntegral 𝓕 μ H J))

open PastItoInputs PastItoAlgebra PhysicalProfile


local instance mixedPastLiteralPoint_circleSigma : MeasurableSpace CircleL2 := borel _
local instance mixedPastLiteralPoint_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩



open Real AddCircle Set Filter WordRecursion ControlledProfile ControlledReferenceLevel SmoothCylinders UniformSmooth
  CutoffWordLevel CutoffWordHistories CutoffCarriers PhysicalScoreChain PhysicalChainArrays
  PhysicalParentGeometry CoveredHistoryGeometry CoveredControlledLaw ControlledOldIntervals
  ControlledFamilyProfileForest GaussianIncrement GaussianConvolution MeasurableGaussianScores
open scoped BigOperators
local instance mixedPastLiteralPoint_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
variable (P : CanonicalCovariance.ProfileParameters) (haP : BoundedSmooth P.coefficient)
variable (v b : ℝ≥0) (hvb : v ≤ b)
variable {X : Type} [MeasurableSpace X] (Z : VariableObservations.Family X 1)
variable (htarget : ∀ x i,(b:ℝ) ≤ (Z.observations x i).target)
variable (hstop : ∀ x i,(b:ℝ) ≤ (Z.observations x i).stop)
variable (F : X→WordRecursion.State 1→ℝ) (hF : UniformBoundedSmooth F)
variable (hFm : Measurable (fun z : X×WordRecursion.State 1=>F z.1 z.2))
local notation "Base" => ControlledReferenceThetaGeometry.level P P.coefficient haP Λ v b hvb Z htarget hstop F hF hFm
local notation "Zero" => Base (0,(0,0))
local notation "U" => MixedPastJointData.pastU 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S v
local notation "Dir" => MixedPastJointData.pastD 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S v

local notation "DataU" => MixedNativeJointHistory.firstData 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
local notation "DataV" => MixedNativeJointHistory.secondData 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S

local notation "Cur" => MixedPastTerminalPairedFields.current 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S P haP v b hvb Z htarget hstop F hF hFm
local notation "Mark" => ControlledFiniteCovarianceFields.point P haP Λ v b hvb Z htarget hstop F hF hFm

local notation "Mean" => MixedPastTerminalFiniteCovariance.terminalMean 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S P haP v b hvb Z htarget hstop F hF hFm
local notation "Point" => MixedPastTerminalFiniteCovariance.point 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S P haP v b hvb Z htarget hstop F hF hFm

/-- The actual finite terminal covariance integrand equals the native
complete conditional Gaussian input at own baseline1/currentV. All old
stops, targets and signed profile direction remain original. -/
theorem point_relative_ae
    (hages:∀x i,(Z.observations x i).stop≤(Z.observations x i).target)
    (hrootstop:∀x i,(Z.observations x i).stop≤(b:ℝ))
    (ρ:Measure X) [IsFiniteMeasure ρ] (k:ℕ):
    ∀ᵐ h ∂historyMeasure (referenceData P P.coefficient haP Λ 0 v b hvb (0,0)) ρ (k+1),
      ∀q:ℝ≥0,(v:ℝ)≤(q:ℝ) → (q:ℝ)=(carrier Zero k).nodeTime h →
      (∀i,(q:ℝ)<((carrier Zero k).observations.observations h.1 i).target) →
      ∀ζ:ℝ,0≤ζ → ζ≤1 → ∀ω:Ω,
      let sgm:=Fin.cons ((q:ℝ)-(v:ℝ)) (fun j=>stops Zero k h.1 j-(v:ℝ))
      let target:=Fin.cons ((q:ℝ)-(v:ℝ)) (fun j=>targets Zero k h.1 j-(v:ℝ))
      let center:=Fin.cons h.2.2 (centers Zero k h.1)
      let c:=BoundedWindowDecomposition.convexProfile P Λ (U ω) (Dir ω) 0 1 ζ
      let e:=fun z=>ControlledProfile.profile P Λ (U ω) (Dir ω) (1,z)-
        ControlledProfile.profile P Λ (U ω) (Dir ω) (0,z)
      Point (k+1) 1 0 1 ζ h ω=
      (1/2:ℝ)*∫x,e x*BoundedCompleteGaussianWord.value P Λ (U ω) (Dir ω) c 1
        ((q:ℝ)-(v:ℝ)) sgm target center
        (fun j=>lower Zero (k+1) h j-(v:ℝ)) (fun j=>upper Zero (k+1) h j-(v:ℝ))
        (MixedPastTerminalData.mean 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
          1 v q (fun j=>stops Zero k h.1 j-(v:ℝ)) (fun j=>targets Zero k h.1 j-(v:ℝ))
          (centers Zero k h.1) h.2.2 ω) true
        (directions Zero ((carrier Zero (k+1)).observations.observations h) (k+1) h)
        (StoppedGaussianFeatures.stoppedRow sgm target center x)
        (rootSelector (k+1) (fun i=>i)) (leafIndex (k+1) (fun i=>i)) (F (rootParameter (k+1) h))
          ∂StoppedGaussianFeatures.historyMeasure ((q:ℝ)-(v:ℝ)):=by
  filter_upwards [ControlledFiniteCovarianceRelative.point_relative_ae
    P haP Λ v b hvb Z htarget hstop F hF hFm hages ρ (k+1)] with h hh
  intro q hvq hqt hgap ζ hζ hζ1 ω sgm target center c e
  have hterminal:(carrier Zero (k+1)).terminal h=(q:ℝ):=hqt.symm
  have hm:=MixedPastTerminalPairedIdentity.current_eq_terminal_mean
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
    P haP v b hvb Z htarget hstop F hF hFm hrootstop true k h q hqt hgap ω
  have hmean:Mean 1 (k+1) h ω=MixedPastTerminalData.mean
      𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
      1 v q (fun j=>stops Zero k h.1 j-(v:ℝ)) (fun j=>targets Zero k h.1 j-(v:ℝ))
      (centers Zero k h.1) h.2.2 ω:=by
    simpa only [MixedPastTerminalFiniteCovariance.terminalMean,sub_self,zero_smul,one_smul,zero_add,ite_true] using hm
  have hsrel:(fun j=>stops Zero (k+1) h j-(v:ℝ))=sgm:=by
    dsimp only [sgm]
    rw [TerminalSuccessorGeometry.stops_succ,←hqt]
    funext j
    exact Fin.cases rfl (fun _=>rfl) j
  have htrel:(fun j=>targets Zero (k+1) h j-(v:ℝ))=target:=by
    dsimp only [target]
    rw [TerminalSuccessorGeometry.targets_succ,←hqt]
    funext j
    exact Fin.cases rfl (fun _=>rfl) j
  have hx:centers Zero (k+1) h=center:=TerminalSuccessorGeometry.centers_succ Zero k h
  have he:=hh (1,(U ω,Dir ω)) (q:ℝ) hvq (by rw [hterminal]) 0 1 ζ hζ hζ1 (Mean 1 (k+1) h ω)
  dsimp only at he
  change ControlledFiniteCovarianceFields.point P haP Λ v b hvb Z htarget hstop F hF hFm
    (1,(U ω,Dir ω)) (k+1) h ((carrier Zero (k+1)).terminal h) 0 1 ζ (Mean 1 (k+1) h ω)=_
  rw [hterminal,he,hmean,hsrel,htrel,hx]

end SHE.MixedPastTerminalFiniteCovarianceRelative
