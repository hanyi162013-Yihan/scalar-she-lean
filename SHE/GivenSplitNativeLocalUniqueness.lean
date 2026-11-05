module
import all SHE.GivenCanonicalCostLimit
public import SHE.GivenCanonicalCostLimit
public import SHE.NativePathLawComparison
public import SHE.NativeStoppedPathComparison
public import SHE.MixedCappedGirsanovDriver
public import SHE.InverseNativeSmoothCommonLaw
public import SHE.StandardChangedHilbertBDG
public import SHE.MixedCanonicalChangedModel
public import SHE.MixedStoppedDifferenceEquation
public import SHE.ItoLocalityTransport
public import SHE.SelectedSmoothCommonLaw
public import SHE.SelectedSmoothIntegratedLaw
import all SHE.CanonicalGivenSharedCompanionCost
public import SHE.CanonicalGivenSharedCompanionCost
public import SHE.CanonicalActualComparisonRecipe
public import SHE.CanonicalComparisonSequence
import all SHE.ActualGaussianSharedCompanionDiagonal
public import SHE.ActualGaussianSharedCompanionDiagonal
public import SHE.CanonicalGivenCompanionFamily
import all SHE.ActualGaussianCompanionUniform
public import SHE.ActualGaussianCompanionUniform
import all SHE.ActualGaussianCompanionAttachment
public import SHE.ActualGaussianCompanionAttachment
public import SHE.CommonComparisonCutoff
public import SHE.CanonicalCompanionExpansion
import all SHE.ActualGaussianMasterBound
public import SHE.ActualGaussianMasterBound
public import SHE.SharedCompanionCostLimit
import all SHE.ActualGaussianNegativeRMS
public import SHE.ActualGaussianNegativeRMS
public import SHE.ActualGaussianBaseCoefficient
public import SHE.ActualGaussianRateFolding
public import SHE.ActualReferenceRateFolding
public import SHE.ActualGaussianMarkCoefficient
public import SHE.NativeMasterRHSCombination
import all SHE.ActualGaussianFiniteRMS
public import SHE.ActualGaussianFiniteRMS
public import SHE.ActualTerminalRMS
import all SHE.ActualGaussianFirstMarkCaps
public import SHE.ActualGaussianFirstMarkCaps
public import SHE.SelectedHigherGaussianPrefixes
public import SHE.SelectedReferenceGaussianPrefixes
public import SHE.FullOrdinaryPrefixEnergy
public import SHE.CanonicalGaussianTerminalLeafRMS
public import SHE.FullFiniteGaussianLeafCap
import all SHE.ActualGaussianFullFamily
public import SHE.ActualGaussianFullFamily
public import SHE.AbsoluteHilbertFinitePrefixes
public import SHE.FullFirstDefectBandPrefixes
import all SHE.ActualGaussianMarkedFamily
import all SHE.ActualFrozenGammaFamily
import all SHE.FullJointGammaMasterAbsolute
public import SHE.ActualGaussianMarkedFamily
public import SHE.ActualFrozenGammaFamily
public import SHE.FullFiniteGaussianRMS
import all SHE.CommonHigherGaussianFamily
import all SHE.CommonReferenceGaussianFamily
import all SHE.FullHigherClockIdentity
import all SHE.FullReferenceClockIdentity
import all SHE.CanonicalGaussianBareRoot
import all SHE.ActualGaussianComponentFamilies
import all SHE.FullFiniteGaussianResidual
public import SHE.ActualGaussianComponentFamilies
public import SHE.FullFiniteGaussianResidual
public import SHE.FullFirstDefectBandPrefixes
public import SHE.CommonHigherGaussianFamily
public import SHE.CommonReferenceGaussianFamily
public import SHE.MixedNativeHigherGaussianTailFamily
public import SHE.FiniteNativeGaussianCutoff
public import SHE.FullHigherClockIdentity
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
set_option linter.style.haveILetI false
namespace SHE.GivenSplitNativeLocalUniqueness
open Filter Topology
open MeasureTheory PredictableL2 NativeHeatObservation NativeObservationNaturality
open FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation StoppedItoInputs
open scoped NNReal ENNReal BoundedContinuousFunction
local instance mixedNativeHigherSharpOutput_realSigma : MeasurableSpace RealL2 := borel _
local instance mixedNativeHigherSharpOutput_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance mixedNativeHigherSharpOutput_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance mixedNativeHigherSharpOutput_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance mixedNativeHigherSharpOutput_blockSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance mixedNativeHigherSharpOutput_blockBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
local instance : MeasurableSpace CircleHeat.CircleL2:=borel _
local instance : BorelSpace CircleHeat.CircleL2:=⟨rfl⟩

open PastItoInputs PastItoAlgebra PhysicalProfile Real AddCircle Set WordRecursion ControlledProfile
  ControlledReferenceLevel SmoothCylinders UniformSmooth CutoffWordLevel CutoffWordHistories
  CutoffCarriers PhysicalScoreChain PhysicalChainArrays PhysicalParentGeometry ProfileStability ProfileL2
open scoped BigOperators
local instance :Fact (0<2*Real.pi):=⟨by positivity⟩
local instance :SecondCountableTopology CircleL2:=
  (_root_.fourierBasis (T:=2*Real.pi)).repr.toHomeomorph.secondCountableTopology


variable {ι:Type}[Fintype ι](Ω:ι→Type)[∀i,MeasurableSpace (Ω i)]
variable (𝓕:∀i,Filtration ℝ≥0 (inferInstance:MeasurableSpace (Ω i)))
  (μ:∀i,Measure (Ω i))[∀i,IsProbabilityMeasure (μ i)]
variable (h:ℝ≥0)(hh:(h:ℝ)≤1)(hpos:0<h)(hNative:(NativeClock.rate*h:ℝ≥0)≤1)
  (D:SmoothApproximation.ScalarData)
local notation "Hor"=>NativeClock.rate*h
local notation "FN" i:max=>PredictableTimeDilation.filtration (𝓕 i)
  (PredictableTimeDilation.clock NativeClock.rate NativeClock.rate_pos)
local notation "Kappa"=>(ScalarReduction.additiveAmplitude D.lower)^2
local notation "KappaPos"=>CanonicalFixedHorizonCompanions.additive_pos D
variable (I₀ I₁:∀i,StandardTerminalIto (C:=RealHaarIntegrand.Columns) (E:=RealL2)
  (PredictableTimeDilation.filtration (𝓕 i) (PredictableTimeDilation.clock NativeClock.rate NativeClock.rate_pos))
  (μ i) (NativeClock.rate*h))
variable (J:∀i,StandardTerminalIto (C:=Both RealHaarInput) (E:=ℝ)
  (PredictableTimeDilation.filtration (𝓕 i) (PredictableTimeDilation.clock NativeClock.rate NativeClock.rate_pos))
  (μ i) (NativeClock.rate*h))
variable (hIJ₀:∀i,StandardScalarNaturality (I₀ i) (leftIntegral
  (PredictableTimeDilation.filtration (𝓕 i) (PredictableTimeDilation.clock NativeClock.rate NativeClock.rate_pos))
  (μ i) (NativeClock.rate*h) (J i)))
  (hIJ₁:∀i,StandardScalarNaturality (I₁ i) (rightIntegral
  (PredictableTimeDilation.filtration (𝓕 i) (PredictableTimeDilation.clock NativeClock.rate NativeClock.rate_pos))
  (μ i) (NativeClock.rate*h) (J i)))
variable (hnull:∀i,NullCompleteFiltration.ContainsNullSets
  (PredictableTimeDilation.filtration (𝓕 i) (PredictableTimeDilation.clock NativeClock.rate NativeClock.rate_pos)) (μ i))
  (hJ:∀i,StandardFiniteIto.Universal
  (PredictableTimeDilation.filtration (𝓕 i) (PredictableTimeDilation.clock NativeClock.rate NativeClock.rate_pos))
  (μ i) (NativeClock.rate*h) (J i))
  (hlocal:∀i,StandardTerminalPastLocality (J i))(hlocalI:∀i,StandardTerminalPastLocality (I₁ i))
  (hFstop:∀i,StandardItoStoppedParameterFubini (J i))
variable (BI0 BI1 Bnext:ι→ℝ≥0)(B:ι→ℕ→ℝ≥0)
  (hBI0:∀i,StandardTerminalBDG16 (I₀ i) (BI0 i))(hBI1:∀i,StandardTerminalBDG16 (I₁ i) (BI1 i))
  (hBDGnext:∀i,StandardTerminalBDGPower 1 (I₁ i) (Bnext i))
  (hBDG:∀i p,0<p→StandardTerminalBDGPower p (J i) (B i p))
variable (u₀:RealL2)
variable (U:∀i,NativeFirstMildData.Data (𝓕 i) (μ i) h ((ScalarReduction.additiveAmplitude D.lower)^2)
  (CanonicalFixedHorizonCompanions.additive_pos D) D.residual_continuous.measurable D.ell_pos D.residual_bounds
  (I₀ i) (I₁ i) u₀)
local notation "Global" LL:max SS:max i:max k:max n:max=>MixedMovingEnergy.globalEnergy
  (FN i) (μ i) Hor (LL k) Kappa KappaPos D.residual_continuous.measurable
  ((D.smooth_boundedSmooth n).smooth.continuous.measurable) D.ell_pos D.residual_bounds
  (D.smooth_bounds n) (I₀ i) (I₁ i) u₀ (SS i k n)

local instance :Fact ((2:ENNReal)≠⊤):=⟨by simp⟩
local instance :SecondCountableTopology RealL2:=
  realCircleIdentification.toHomeomorph.secondCountableTopology
variable (hNovikov:∀i,StandardTerminalNovikov (J i))
  (hGirsanov:∀i,StandardTerminalGirsanov (J i))
  (hRecognizedBDG:∀i,StandardChangedHilbertBDG
    (PredictableTimeDilation.filtration (𝓕 i)
      (PredictableTimeDilation.clock NativeClock.rate NativeClock.rate_pos))
    (μ i) (NativeClock.rate*h) (J i))

/- The only stochastic assumptions below are the explicit ordinary
integration, Gaussian, Brownian recognition, BDG and Girsanov packages. -/
include hh hpos hNative hIJ₀ hIJ₁ hnull hJ hlocal hlocalI hFstop hBI0 hBI1 hBDGnext hBDG
  hNovikov hGirsanov hRecognizedBDG in
/-- Fixed-interval uniqueness for GIVEN split native mild solutions.
Original one-noise reconstruction and arbitrary-time continuation are
separate from this statement. All actual comparison choices are internal. -/
theorem laws_eq:
    ∀i j:ι,NativePathLawComparison.law Hor (μ i) (U i).value (U i).continuous=
      NativePathLawComparison.law Hor (μ j) (U j).value (U j).continuous:=by
  classical
  have hHor:0<Hor:=mul_pos NativeClock.rate_pos hpos
  have hHreal:(Hor:ℝ)≤1:=by exact_mod_cast hNative
  obtain ⟨Λ,hΛ1,hΛ,SS,hSS,index,hindex,hindext,hlimits⟩:=
    GivenCanonicalCostLimit.exists_diagonal Ω 𝓕 μ h hh hpos hNative D I₀ I₁ J
      hIJ₀ hIJ₁ hnull hJ hlocal hlocalI hFstop BI0 BI1 Bnext B hBI0 hBI1 hBDGnext hBDG u₀ U
  have hΛ0(k:ℕ):0≤Λ k:=zero_le_one.trans (hΛ1 k)
  have hLC(n:ℕ):∃L:ℝ≥0,LipschitzWith L (fun z=>(D.smoothCoefficient n z:ℂ)):=by
    obtain ⟨L,hL⟩:=D.smooth_lipschitz n
    exact ⟨L,by simpa only [one_mul,Function.comp_def] using Complex.isometry_ofReal.lipschitzWith.comp hL⟩
  choose Lip hLip using hLC
  have hB16(i:ι):StandardTerminalBDG16 (J i) (B i 8):=
    (standardTerminalBDGPower_eight (J i) (B i 8)).mp (hBDG i 8 (by omega))
  let Ch(i:ι)(k:ℕ):=Classical.choice (MixedCanonicalChangedModel.exists_data
    (FN i) (μ i) Hor (Λ k) Kappa KappaPos D.residual_continuous.measurable
    ((D.smooth_boundedSmooth (index k)).smooth.continuous.measurable)
    D.ell_pos D.residual_bounds (D.smooth_bounds (index k)) (I₀ i) (I₁ i) u₀
    (SS i k (index k)) (J i) (hIJ₀ i) (hIJ₁ i) (hΛ0 k) hHreal D.beta_pos
    D.holderConstant_nonneg (D.smooth_holder (index k)) (hLip (index k))
    (hNovikov i) (hGirsanov i) hHor (hnull i) (hlocal i) (B i 1) (B i 8)
    (hBDG i 1 (by omega)) (hB16 i) (hRecognizedBDG i))
  letI (i:ι)(k:ℕ):IsProbabilityMeasure (Ch i k).Q:=(Ch i k).probability
  let W(i:ι)(k:ℕ):=MixedCanonicalChangedModel.Data.solution
    (FN i) (μ i) Hor (Λ k) Kappa KappaPos D.residual_continuous.measurable
    ((D.smooth_boundedSmooth (index k)).smooth.continuous.measurable)
    D.ell_pos D.residual_bounds (D.smooth_bounds (index k)) (I₀ i) (I₁ i) u₀
    (SS i k (index k)) (J i) (hΛ0 k) hHreal D.beta_pos D.holderConstant_nonneg
    (D.smooth_holder (index k)) (Ch i k)
  let V(i:ι)(k:ℕ):ℝ≥0→Ω i→RealL2:=(SS i k (index k)).second
  have hVc(i:ι)(k:ℕ):∀ω,Continuous (fun t=>V i k t ω):=(SS i k (index k)).second_continuous
  have hVm(i:ι)(k:ℕ):Measurable (Function.uncurry (V i k)):=
    ((SS i k (index k)).second_predictable.mono (predictable_le_product (FN i))).measurable
  have hUm(i:ι):Measurable (Function.uncurry (U i).value):=
    ((U i).predictable.mono (predictable_le_product (FN i))).measurable
  let cost(i:ι)(k:ℕ):ℝ:=((Λ k)^2/Kappa)*Global Λ SS i k (index k)
  have hcost(i:ι)(k:ℕ):0≤cost i k:=mul_nonneg (div_nonneg (sq_nonneg _) (KappaPos).le)
    (integral_nonneg (fun _=>sq_nonneg _))
  have hcostlim(i:ι):Tendsto (cost i) atTop (𝓝 0):=by
    convert (hlimits i).1.mul_const Kappa⁻¹ using 1
    · funext k
      dsimp [cost]
      ring
    · simp
  have hEq(i:ι)(k:ℕ):(fun z:ℝ≥0×Ω i=>‖(U i).value z.1 z.2-V i k z.1 z.2‖^2)=
      (fun z:ℝ≥0×Ω i=>‖(SS i k (index k)).second z.1 z.2-(SS i k (index k)).first z.1 z.2‖^2):=by
    funext z
    rw [hSS i k (index k),norm_sub_rev]
  have hi(i:ι)(k:ℕ):Integrable
      (fun z:ℝ≥0×Ω i=>‖(U i).value z.1 z.2-V i k z.1 z.2‖^2) (energyMeasure (μ i) Hor):=by
    rw [hEq i k]
    exact MixedMovingEnergy.global_integrable (FN i) (μ i) Hor (Λ k) Kappa KappaPos
      D.residual_continuous.measurable ((D.smooth_boundedSmooth (index k)).smooth.continuous.measurable)
      D.ell_pos D.residual_bounds (D.smooth_bounds (index k)) (I₀ i) (I₁ i) u₀ (SS i k (index k))
      (J i) (hIJ₀ i) (hIJ₁ i) (hΛ0 k) hHreal (B i 1) (hBDG i 1 (by omega))
  have he(i:ι):Tendsto (fun k=>∫z:ℝ≥0×Ω i,‖(U i).value z.1 z.2-V i k z.1 z.2‖^2 ∂energyMeasure (μ i) Hor)
      atTop (𝓝 0):=by
    simp_rw [hEq i]
    exact (hlimits i).2
  letI:MeasurableSpace (Lp RealL2 2 (SHE.timeMeasure (Hor:ℝ))):=borel _
  letI:BorelSpace (Lp RealL2 2 (SHE.timeMeasure (Hor:ℝ))):=⟨rfl⟩
  let canonical(i:ι)(k:ℕ):ProbabilityMeasure (Lp RealL2 2 (SHE.timeMeasure (Hor:ℝ))):=
    ProbabilityMeasure.map (⟨(Ch i k).Q,inferInstance⟩:ProbabilityMeasure (Ω i))
      (NativeContinuousPath.integrated Hor (W i k).value (W i k).continuous)
  have hcanonical(i j:ι)(k:ℕ):canonical i k=canonical j k:=by
    apply Subtype.ext
    exact SelectedSmoothCommonLaw.integrated
      (FN i) (Ch i k).Q Hor hHreal Kappa KappaPos
      ((D.smooth_boundedSmooth (index k)).smooth.continuous.measurable) D.ell_pos
      (D.smooth_bounds (index k)) D.beta_pos D.holderConstant_nonneg (D.smooth_holder (index k))
      (Ch i k).K (Ch i k).A0 (Ch i k).A1 u₀ (hLip (index k)) hHor (Ch i k).smooth
      (FN j) (Ch j k).Q (Ch j k).K (Ch j k).A0 (Ch j k).A1 (Ch j k).smooth
  have hagree(i:ι)(k:ℕ):∀ᵐω∂(Ch i k).Q,
      PredictableEnergyCap.accumulated
        (MixedCappedControl.raw (FN i) (μ i) Hor (Λ k) Kappa KappaPos
          D.residual_continuous.measurable ((D.smooth_boundedSmooth (index k)).smooth.continuous.measurable)
          D.ell_pos D.residual_bounds (D.smooth_bounds (index k)) (I₀ i) (I₁ i) u₀ (SS i k (index k))) Hor ω<1→
        ∀t:ℝ≥0,t≤Hor→V i k t ω=(W i k).value t ω:=by
    have hloc:StandardTerminalPastLocality (Ch i k).A1:=
      NativeHilbertPastLocality.right (FN i) (Ch i k).Q Hor (Ch i k).A1 (Ch i k).K
        (Ch i k).smooth.naturality1 (Ch i k).smooth.locality
    exact MixedStoppedDifferenceEquation.path_agreement
      (𝓕:=FN i) (μ:=μ i) (H:=Hor) (Λ:=Λ k) (κ:=Kappa) (hκ:=KappaPos)
      (haU:=D.residual_continuous.measurable)
      (haV:=(D.smooth_boundedSmooth (index k)).smooth.continuous.measurable)
      (hell:=D.ell_pos) (hbU:=D.residual_bounds) (hbV:=D.smooth_bounds (index k))
      (I₀:=I₀ i) (I₁:=I₁ i) (u₀:=u₀) (S:=SS i k (index k))
      (Q:=(Ch i k).Q) (A0:=(Ch i k).A0) (A1:=(Ch i k).A1)
      (hΛ:=hΛ0 k) (hH:=hHreal) (hV:=(Ch i k).mild) (W:=W i k)
      (K:=(Ch i k).K) (hA0:=(Ch i k).smooth.naturality0)
      (hA1:=(Ch i k).smooth.naturality1) (hlocal:=hloc) (hpos:=hHor)
      (hcoef:=by
        have hc:=NonlinearHaarIntegrand.coefficientField_measurable
          ((D.smooth_boundedSmooth (index k)).smooth.continuous.measurable)
          D.ell_pos (D.smooth_bounds (index k)) D.beta_pos D.holderConstant_nonneg
          (D.smooth_holder (index k))
        exact hc.mono le_rfl OpensMeasurableSpace.borel_le) (hLip (index k))
  have hchange(i:ι)(k:ℕ)(f:Lp RealL2 2 (SHE.timeMeasure (Hor:ℝ))→ᵇℝ):
      |(∫ω,f (NativeContinuousPath.integrated Hor (V i k) (hVc i k) ω) ∂μ i)-
        (∫x,f x ∂canonical i k)|≤2*‖f‖*(Real.sqrt (cost i k)+cost i k):=by
    let Raw:=MixedCappedControl.raw (FN i) (μ i) Hor (Λ k) Kappa KappaPos
      D.residual_continuous.measurable ((D.smooth_boundedSmooth (index k)).smooth.continuous.measurable)
      D.ell_pos D.residual_bounds (D.smooth_bounds (index k)) (I₀ i) (I₁ i) u₀ (SS i k (index k))
    have hm:Measurable (PredictableEnergyCap.accumulated Raw Hor):=
      (PredictableEnergyCap.accumulated_adapted (FN i) Raw
        (MixedCappedControl.adapted (FN i) (μ i) Hor (Λ k) Kappa KappaPos
          D.residual_continuous.measurable ((D.smooth_boundedSmooth (index k)).smooth.continuous.measurable)
          D.ell_pos D.residual_bounds (D.smooth_bounds (index k)) (I₀ i) (I₁ i) u₀ (SS i k (index k)))
        (MixedCappedControl.continuous (FN i) (μ i) Hor (Λ k) Kappa KappaPos
          D.residual_continuous.measurable ((D.smooth_boundedSmooth (index k)).smooth.continuous.measurable)
          D.ell_pos D.residual_bounds (D.smooth_bounds (index k)) (I₀ i) (I₁ i) u₀ (SS i k (index k))) Hor).measurable.mono ((FN i).le Hor) le_rfl
    apply NativeStoppedPathComparison.bound Hor (μ i) (Ch i k).Q (Ch i k).changed_ac
      (measurableSet_le measurable_const hm) (cost i k) (Ch i k).compare
      (V i k) (W i k).value (hVc i k) (W i k).continuous (hVm i k)
      (((W i k).predictable.mono (predictable_le_product (FN i))).measurable)
      ?_ (canonical i k) rfl f
    filter_upwards [(Ch i k).original_ac.ae_le (hagree i k)] with ω hω hb
    exact hω (lt_of_not_ge hb)
  intro i j
  apply NativePathLawComparison.laws_eq Hor hHor (μ i) (μ j)
    (U i).value (U j).value (U i).continuous (U j).continuous (hUm i) (hUm j)
    (V i) (V j) (hVc i) (hVc j) (hVm i) (hVm j) (hi i) (hi j) (he i) (he j)
    (canonical i) (cost i) (cost j) (hcost i) (hcost j) (hcostlim i) (hcostlim j) (hchange i)
  intro k f
  rw [hcanonical i j k]
  exact hchange j k f

end SHE.GivenSplitNativeLocalUniqueness
