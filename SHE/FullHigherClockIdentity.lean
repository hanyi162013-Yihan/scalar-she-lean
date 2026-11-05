module
public import SHE.MixedNativeHigherGaussianFamily
public import SHE.CanonicalGaussianBareRoot
public import SHE.FullOrdinaryClockIdentity
public import SHE.MixedNativeReferenceGaussianFamily
public import SHE.MixedNativeHigherGaussianBand
public import SHE.NativeGaussianWindowCutoff
public import SHE.NativeFullRateCap
public import SHE.HilbertENNRateTails
public import SHE.MixedNativeHigherFullOutput
public import SHE.CanonicalGaussianRootBands
public import SHE.MixedNativeHigherMovingRate
public import SHE.MixedNativeMovingEnvelopeRate
public import SHE.MixedNativeHigherSharpOutput
public import SHE.MixedNativeHigherSharpInitial
public import SHE.NativeOutputTimePatch
public import SHE.MixedNativeHigherMovingOutput
public import SHE.NativeOriginalOutputParameter
public import SHE.MovingNativePredictableAverages
public import SHE.MixedNativeHigherMovingEnergy
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
namespace SHE.FullHigherClockIdentity
open MeasureTheory PredictableL2 NativeHeatObservation NativeObservationNaturality
open FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation StoppedItoInputs
open scoped NNReal ENNReal
local instance mixedNativeHigherSharpOutput_realSigma : MeasurableSpace RealL2 := borel _
local instance mixedNativeHigherSharpOutput_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance mixedNativeHigherSharpOutput_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance mixedNativeHigherSharpOutput_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance mixedNativeHigherSharpOutput_blockSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance mixedNativeHigherSharpOutput_blockBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
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


local instance mixedNativeHigherSharpOutput_circleSigma : MeasurableSpace CircleL2 := borel _
local instance mixedNativeHigherSharpOutput_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩



open Real AddCircle Set Filter WordRecursion ControlledProfile ControlledReferenceLevel SmoothCylinders UniformSmooth
  CutoffWordLevel CutoffWordHistories CutoffCarriers PhysicalScoreChain PhysicalChainArrays
  PhysicalParentGeometry CoveredHistoryGeometry CoveredControlledLaw ControlledOldIntervals
  ControlledFamilyProfileForest GaussianIncrement GaussianConvolution MeasurableGaussianScores
open ProfileStability ProfileL2
open HistoryProductMeasure
open scoped BigOperators
local instance mixedNativeHigherSharpOutput_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
local instance mixedNativeHigherSharpOutput_nativeSecond:SecondCountableTopology CircleL2:=
  (_root_.fourierBasis (T:=2*Real.pi)).repr.toHomeomorph.secondCountableTopology
variable (P:CanonicalCovariance.ProfileParameters)(haP:BoundedSmooth P.coefficient)
variable (J:StandardTerminalIto (C:=Both RealHaarInput) (E:=ℝ) 𝓕 μ H)
variable (hIJ₀:StandardScalarNaturality I₀ (leftIntegral 𝓕 μ H J))
variable (hIJ₁:StandardScalarNaturality I₁ (rightIntegral 𝓕 μ H J))
variable (hnull:NullCompleteFiltration.ContainsNullSets 𝓕 μ)(hJ:StandardFiniteIto.Universal 𝓕 μ H J)
variable (hAs:BoundedSmooth (fun z=>κ+aV z))
variable (F:HeatCircle→WordRecursion.State 1→ℝ)(hF:UniformBoundedSmooth F)
variable (hFm:Measurable (fun z:HeatCircle×WordRecursion.State 1=>F z.1 z.2))
def original(w:ℝ≥0)(hL:1≤Λ){ρ:ℝ}(hρ:0≤ρ)(k:ℕ)(z:ℝ≥0×Ω):CircleL2:=
  MixedNativeHigherOriginalEnergy.value 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
    J hIJ₀ hIJ₁ hnull hJ P hAs (z.1-w) z.1 tsub_le_self (ControlledScalarReference.observations z.1)
      (fun _=>rfl) (fun _=>rfl) F hF hFm hL hρ k z.2

def patched(w:ℝ≥0)(hL:1≤Λ){ρ:ℝ}(hρ:0≤ρ)(k:ℕ):ℝ≥0×Ω→CircleL2:=
  NativeOutputTimePatch.field w
    (MixedNativeHigherInitialOutput.output
      𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP w F hF hFm J hIJ₀ hIJ₁ hnull hJ hAs hL hρ k)
    (MixedNativeHigherMovingOutput.output
      𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P w (ControlledScalarReference.observations w)
        F hF hFm J hIJ₀ hIJ₁ hnull hJ hAs (fun _=>rfl) (fun _=>rfl) hL hρ k)
local notation "Original"=>original
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P J hIJ₀ hIJ₁ hnull hJ hAs
local notation "Patched"=>patched
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP J hIJ₀ hIJ₁ hnull hJ hAs

theorem root_congr(G:HeatCircle→WordRecursion.State 1→ℝ)(hG:UniformBoundedSmooth G)
    (hGm:Measurable (fun z:HeatCircle×WordRecursion.State 1=>G z.1 z.2))(he:F=G)
    (w:ℝ≥0)(hL:1≤Λ){ρ:ℝ}(hρ:0≤ρ)(k:ℕ):
    Original F hF hFm w hL hρ k=Original G hG hGm w hL hρ k:=by
  subst G
  rfl

/-- The true initial/completed noise patch is the literal original-J
higher output at b=t and v=(t-window)^+, pointwise for every positive
original output time up to H. -/
theorem identity(w:ℝ≥0)(hL:1≤Λ){ρ:ℝ}(hρ:0≤ρ)(k:ℕ)
    (t:ℝ≥0)(ht:0<t)(htH:t≤H)(ω:Ω):
    Patched F hF hFm w hL hρ k (t,ω)=Original F hF hFm w hL hρ k (t,ω):=by
  unfold patched NativeOutputTimePatch.field
  by_cases htw:t≤w
  · rw [if_pos htw]
    unfold MixedNativeHigherInitialOutput.output
    rw [if_pos (show 0<t ∧ t≤w from ⟨ht,htw⟩)]
    unfold MixedNativeHigherInitialEnergy.output
    have hT:InitialNativeKernelFibre.terminal Λ u₀ P haP w
        (InitialRetainedTriangleEnergy.clippedTime w (t:ℝ))=t:=by
      apply Subtype.ext
      change ClippedCovariance.clip 0 (w:ℝ) (t:ℝ)=(t:ℝ)
      exact ClippedCovariance.clip_eq ⟨t.2,by exact_mod_cast htw⟩
    unfold original
    simp only [Prod.fst,Prod.snd,hT,tsub_eq_zero_of_le htw]
  · rw [if_neg htw]
    unfold MixedNativeHigherMovingOutput.output
    rw [if_pos (show t-w+w≤H from (tsub_add_cancel_of_le (le_of_lt (lt_of_not_ge htw))).trans_le htH)]
    unfold MixedNativeHigherMovingEnergy.output original
    simp only [Prod.fst,Prod.snd,FullOrdinaryClockIdentity.observations_shift,
      tsub_add_cancel_of_le (le_of_lt (lt_of_not_ge htw))]

variable (D:SmoothApproximation.ScalarData)(n j:ℕ)
local notation "CF"=>CanonicalGaussianRootBands.test D n (fun _:HeatCircle=>(1:ℝ)) (j+1)
local notation "CU"=>CanonicalGaussianRootBands.uniform D n (fun _:HeatCircle=>(1:ℝ)) (W:=1) zero_le_one (fun _=>by norm_num) (j+1)
local notation "CM"=>CanonicalGaussianRootBands.measurable D n (fun _:HeatCircle=>(1:ℝ)) measurable_const (j+1)
local notation "Bare"=>CanonicalGaussianBareRoot.test D n (j+1)
local notation "BU"=>CanonicalGaussianBareRoot.uniform D n (j+1)
local notation "BM"=>CanonicalGaussianBareRoot.measurable D n (j+1)

/-- Exact canonical Gaussian band identity to the bare RootFamily_j
used by ActualFiniteGaussianComparison; no version or analytic premise. -/
theorem canonical(hL:1≤Λ){ρ:ℝ}(hρ:0≤ρ)(k:ℕ)(t:ℝ≥0)(ht:0<t)(htH:t≤H)(ω:Ω):
    MixedNativeHigherGaussianFamily.actual
      𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP D n
        (fun _:HeatCircle=>(1:ℝ)) measurable_const (W:=1) zero_le_one (fun _=>by norm_num)
          J hIJ₀ hIJ₁ hnull hJ hAs hL hρ k (j+1) (t,ω)=
    Original Bare BU BM (RemainderBandSpans.span D.beta (j+1)) hL hρ k (t,ω):=by
  have hi:=identity 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP
    J hIJ₀ hIJ₁ hnull hJ hAs CF CU CM (RemainderBandSpans.span D.beta (j+1)) hL hρ k t ht htH ω
  have hr:=root_congr 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P
    J hIJ₀ hIJ₁ hnull hJ hAs CF CU CM Bare BU BM (CanonicalGaussianBareRoot.test_one D n (j+1))
      (RemainderBandSpans.span D.beta (j+1)) hL hρ k
  exact hi.trans (congrFun hr (t,ω))
end SHE.FullHigherClockIdentity
