module

public import SHE.MixedPastProfileDerivative
public import SHE.MixedPastOmittedMarkFields
public import SHE.MixedPastLiteralOmitted
public import SHE.MixedPastNativeOmitted
public import SHE.ControlledThetaOmittedFields
public import SHE.ControlledFamilyProfileMarkFields
public import SHE.MixedPastLiteralFields
public import SHE.JointInterpolationFields
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
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 2200000

namespace SHE.MixedPastNativeBaselineLeaf
open MeasureTheory PredictableL2 NativeHeatObservation NativeObservationNaturality
open FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation StoppedItoInputs
open scoped NNReal ENNReal
local instance mixedPastOmittedLeafMoments_realSigma : MeasurableSpace RealL2 := borel _
local instance mixedPastOmittedLeafMoments_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance mixedPastOmittedLeafMoments_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance mixedPastOmittedLeafMoments_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance mixedPastOmittedLeafMoments_blockSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance mixedPastOmittedLeafMoments_blockBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
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


local instance mixedPastOmittedLeafMoments_circleSigma : MeasurableSpace CircleL2 := borel _
local instance mixedPastOmittedLeafMoments_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩
variable {n : ℕ}



open Real AddCircle Set Filter WordRecursion ControlledProfile ControlledReferenceLevel SmoothCylinders UniformSmooth
  CutoffWordLevel CutoffWordHistories CutoffCarriers PhysicalScoreChain PhysicalChainArrays
  PhysicalParentGeometry CoveredHistoryGeometry CoveredControlledLaw ControlledOldIntervals
  ControlledFamilyProfileForest GaussianIncrement GaussianConvolution MeasurableGaussianScores
open scoped BigOperators
local instance mixedPastOmittedLeafMoments_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
variable (P : CanonicalCovariance.ProfileParameters) (haP : BoundedSmooth P.coefficient)
variable (v b : ℝ≥0) (hvb : v ≤ b)
variable {X : Type} [MeasurableSpace X] {n : ℕ} (Z : VariableObservations.Family X n)
variable (htarget : ∀ x i,(b:ℝ) ≤ (Z.observations x i).target)
variable (hstop : ∀ x i,(b:ℝ) ≤ (Z.observations x i).stop)
variable (F : X→WordRecursion.State n→ℝ) (hF : UniformBoundedSmooth F)
variable (hFm : Measurable (fun z : X×WordRecursion.State n=>F z.1 z.2))
local notation "Base" => ControlledReferenceThetaGeometry.level P P.coefficient haP Λ v b hvb Z htarget hstop F hF hFm
local notation "Zero" => Base (0,(0,0))
local notation "U" => MixedPastJointData.pastU 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S v
local notation "Dir" => MixedPastJointData.pastD 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S v


/-- Literal native-first baseline leaf. Its profile multiplier stays
outside the entire Gaussian word and remains measurable at the past. -/
def value (k:ℕ) (θ:ℝ) (q:ℝ≥0) (h:History X k)
    (E:WordRecursion.State (n+k)) (j0:Fin k) (ω:Ω):ℝ:=
  MixedPastOmittedMarkFields.leafInput
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
    P haP v b hvb Z htarget hstop F hF hFm k θ h j0 ω *
  MixedPastNativeOmitted.average
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
    P haP v b hvb Z htarget hstop F hF hFm k θ q h E j0 ω

include hIJ₀ hIJ₁ in
/-- Actual omitted-baseline input and Gaussian word may be correlated.
The true F_v derivative is used as a conditional weight BEFORE spatial
averaging. Only its genuine pointwise sample energy is required here. -/
theorem leaf_moment_ae (hlocal : StandardTerminalPastLocality J) (hΛ : 0≤Λ)
    (hsmall : ProfileStability.memoryConstant P.lower P.holder P.exponent*
      ProfileVolterra.powerConstant ((P.exponent-2)/4)*P.horizon^(P.exponent/4)≤1/2)
    (hages : ∀ x i,(Z.observations x i).stop≤(Z.observations x i).target)
    (hspan : (b:ℝ)-(v:ℝ)≤P.horizon) (ρ : Measure X) [IsFiniteMeasure ρ] (k : ℕ) :
    ∀ᵐ h ∂historyMeasure (referenceData P P.coefficient haP Λ 0 v b hvb (0,0)) ρ k,
      ∀ q : ℝ≥0,v≤q→q≤H→(q:ℝ)<(carrier Zero k).terminal h→
      ∀ hp : StrictHistory Zero k h,SmallHistory Zero (uniformHorizon n) k h→
      ∀ θ : ℝ,|θ|≤1→∀ A0 ν : ℝ,0≤A0→0≤ν→
      (∀ j,j≤k→∀ z,‖iteratedFDeriv ℝ j (F (rootParameter k h)) z‖≤A0*ν^j)→
      ∀ E : WordRecursion.State (n+k),
      E∈(Matrix.toEuclideanCLM (𝕜:=ℝ) (NativeFirstScoreReserve.covariance P
        (fun i=>stops Zero k h i-(v:ℝ)) (fun i=>targets Zero k h i-(v:ℝ))
        (centers Zero k h) ((q:ℝ)-(v:ℝ)))).range →
      ∀ j0 : Fin k,∀ B0 : ℝ≥0,StandardTerminalBDGPower (k+2) J B0→
      let e:=MixedPastOmittedMarkFields.leafInput
        𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
        P haP v b hvb Z htarget hstop F hF hFm k θ h j0
      Integrable (fun ω=>|e ω|^2) μ→
      let oldEnvelope:=timeWeight Zero (fraction P*P.lower) (uniformConstant n) k h*
        OrderedHeatForests.parentDensity 2 (by norm_num) k (targets Zero k h)
          (carrier_orderedTimes Zero hages k h hp) (centers Zero k h)
      let sharp:=NativeOmittedTimeTotal.total (d:=n) P
        (fun j=>lower Zero k h j-(v:ℝ)) (fun j=>upper Zero k h j-(v:ℝ))
        (fun j=>targets Zero k h (leafIndex k (fun i=>i) j)-(v:ℝ)) j0 A0 ν
      let G:=value
        𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
        P haP v b hvb Z htarget hstop F hF hFm k θ q h E j0
      Integrable (fun ω=>|G ω|^2) μ ∧
        (∫ ω,|G ω|^2 ∂μ)≤
          NativeOmittedCompleteWord.momentConstant P k k j0 1
            ((k:ℝ)*(NativeHybridMoments.momentConstant (k+2) B0 κ M)^P.exponent)*
              (oldEnvelope*Real.sqrt (scoreVariance (NativeFirstScoreReserve.covariance P
                (fun i=>stops Zero k h i-(v:ℝ)) (fun i=>targets Zero k h i-(v:ℝ))
                (centers Zero k h) ((q:ℝ)-(v:ℝ))) E)*sharp)^2*(∫ ω,|e ω|^2 ∂μ) := by
  filter_upwards [MixedPastNativeOmitted.weighted_even_moment_ae
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S J hIJ₀ hIJ₁
    P haP v b hvb Z htarget hstop F hF hFm hlocal hΛ hages hspan ρ k] with h hh
  intro q hvq hqH hqt hp hs θ hθ A0 ν hA0 hν hjet E hE j0 B0 hBDG e hei oldEnvelope sharp G
  have he : Measurable[𝓕 v] e:=MixedPastOmittedMarkFields.leaf_input_past_measurable
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
    P haP v b hvb Z htarget hstop F hF hFm hΛ hsmall k θ h j0
  have hw : Measurable[𝓕 v] (fun ω=>|e ω|^2) := by
    letI : MeasurableSpace Ω:=𝓕 v
    exact (continuous_abs.measurable.comp he).pow_const 2
  have hbound:=hh q hvq hqH hqt hp hs θ hθ A0 ν hA0 hν hjet E hE j0 1 (by norm_num) B0
    (by simpa only [one_mul] using hBDG) (fun ω=>|e ω|^2) hw
    (fun ω=>sq_nonneg _) hei
  have heq (ω : Ω) : |G ω|^2=|e ω|^2*
      |MixedPastNativeOmitted.average 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
        P haP v b hvb Z htarget hstop F hF hFm k θ q h E j0 ω|^2 := by
    simp only [G,value,abs_mul,mul_pow,e]
  simpa only [one_mul,heq,oldEnvelope,sharp] using hbound


end SHE.MixedPastNativeBaselineLeaf
