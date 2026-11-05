module
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
namespace SHE.GivenCanonicalCostLimit
open Filter Topology
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
include hh hpos hNative hIJ₀ hIJ₁ hnull hJ hlocal hlocalI hFstop hBI0 hBI1 hBDGnext hBDG in
/-- Fully instantiated actual comparison: all profile, moment, band,
cutoff, damping and common smoothing choices are internal. Inputs are
only the GIVEN rough solutions and the ordinary stochastic packages. -/
theorem exists_diagonal:
    ∃(Λ:ℕ→ℝ),(∀k,1≤Λ k) ∧ Tendsto Λ atTop atTop ∧
      ∃SS:∀i k n,MixedNativeAdditiveResidualPair.Solution (FN i) (μ i) Hor (Λ k) Kappa KappaPos
        D.residual_continuous.measurable ((D.smooth_boundedSmooth n).smooth.continuous.measurable)
        D.ell_pos D.residual_bounds (D.smooth_bounds n) (I₀ i) (I₁ i) u₀ u₀,
        (∀i k n,(SS i k n).first=(U i).value) ∧
        ∃index:ℕ→ℕ,StrictMono index ∧ Tendsto index atTop atTop ∧
          ∀i:ι,Tendsto (fun k=>(Λ k)^2*Global Λ SS i k (index k)) atTop (𝓝 0) ∧
            Tendsto (fun k=>Global Λ SS i k (index k)) atTop (𝓝 0):=by
  have hHor:0<Hor:=mul_pos NativeClock.rate_pos hpos
  have hHreal:(Hor:ℝ)≤1:=by exact_mod_cast hNative
  obtain ⟨T,hT,hT1,hprofile,ζ,p,hparams,hsmall,Bcut,hBcut,hcuts⟩:=
    CanonicalActualComparisonRecipe.exists_recipe D Hor hHor
  obtain ⟨hζ,hζβ,hp,hα,hαhalf,horder,horderref,htail,hcur,hpast,hgood,hbad⟩:=hparams
  let N:=SHE.depth D.beta
  obtain ⟨Λ,cut,hΛ1,hΛ,hfreq,hlow,hcut⟩:=
    CanonicalComparisonSequence.exists_sequence D hT hT1 hprofile Hor hHor N
  have hr:0<SHE.rho D.beta:=by dsimp [SHE.rho];linarith [D.beta_le]
  have hrh:SHE.rho D.beta<1/2:=by dsimp [SHE.rho];linarith [D.beta_pos]
  have hc0:0≤SHE.chi D.beta:=by dsimp [SHE.chi];linarith [D.beta_le]
  have hc1:SHE.chi D.beta<1:=by dsimp [SHE.chi];linarith [D.beta_pos]
  have hcm:SHE.chi D.beta<D.beta+2*SHE.rho D.beta:=by dsimp [SHE.chi,SHE.rho];linarith [D.beta_pos]
  have hRef:0<ActualReferenceMasterClosure.referenceExponent D.beta:=by
    dsimp [ActualReferenceMasterClosure.referenceExponent];linarith [D.beta_le]
  have hRef1:ActualReferenceMasterClosure.referenceExponent D.beta<1:=by
    dsimp [ActualReferenceMasterClosure.referenceExponent];linarith [D.beta_pos]
  have he:0<D.beta/100:=by positivity [D.beta_pos]
  have hehalf:D.beta/100<1/2:=by linarith [D.beta_le]
  have heβ:D.beta/100<D.beta:=by linarith [D.beta_pos]
  have hLeaf:D.beta/100≤D.beta/4:=by linarith [D.beta_pos]
  have ho0:1≤(2:ℝ)*(1-D.beta/2):=by linarith [D.beta_le]
  have ho1:1≤(2:ℝ)*(1-(D.beta/2)/D.beta):=by
    have hb:D.beta≠0:=ne_of_gt D.beta_pos
    field_simp
    linarith [D.beta_pos]
  have hqh(i:Fin 4):0<NativeFullRateCap.degree
      (NativeBandFrequencyRates.currentDegree D.beta (SHE.rho D.beta) (SHE.chi D.beta) ζ)
      (NativeBandFrequencyRates.pastDegree D.beta ζ) (SignedNativeBandFrequency.goodDegree D.beta ζ ζ)
      (SignedNativeBandFrequency.badDegree D.beta 20 ζ) i:=by
    fin_cases i
    · exact hcur
    · exact hpast
    · exact hgood
    · exact (by norm_num: (0:ℝ)<16).trans hbad
  have hqr(k:ℕ)(hk:k<N)(i:Fin 3):0<MixedNativeReferenceGaussianFamily.degrees D.beta (SHE.rho D.beta)
      (D.beta/100) (D.beta/100) (k+1) i:=NativeReferenceMasterCoefficient.degrees_pos D.beta_pos D.beta_le (k+1) i
  have hB16(i:ι):StandardTerminalBDG16 (J i) (B i 8):=
    (standardTerminalBDGPower_eight (J i) (B i 8)).mp (hBDG i 8 (by omega))
  obtain ⟨SS,hSS,L,index,hi,hit,happrox,hcost⟩:=CanonicalGivenSharedCompanionCost.exists_diagonal
    (Ω:=Ω) (𝓕:=𝓕) (μ:=μ) (h:=h)
    (hh:=hh) (hpos:=hpos) (D:=D) (κ:=Kappa)
    (hκ:=KappaPos) (hκD:=rfl) (I₀:=I₀) (I₁:=I₁)
    (u₀:=fun _=>u₀) (J:=J) (hIJ₀:=hIJ₀) (hIJ₁:=hIJ₁)
    (hnull:=hnull) (hJ:=hJ) (hlocal:=hlocal) (hlocalI:=hlocalI)
    (hFstop:=hFstop) (hT:=hT) (hT1:=hT1) (hsmall:=hprofile)
    (Λ:=Λ) (hΛ1:=hΛ1) (hΛ:=hΛ) (cut:=cut)
    (N:=N) (ρ:=SHE.rho D.beta) (χ:=SHE.chi D.beta) (χref:=ActualReferenceMasterClosure.referenceExponent D.beta)
    (η:=ζ) (ε:=ζ) (tail:=20) (ζ:=ζ)
    (εref:=D.beta/100) (ηref:=D.beta/100) (hρ:=hr) (hρhalf:=hrh)
    (hρeq:=rfl) (hχ0:=hc0) (hχ1:=hc1) (hm:=hcm)
    (hχeq:=rfl) (hα:=hα) (hαhalf:=hαhalf) (hζ:=hζ)
    (hη:=hζ) (hχref:=hRef) (hχref1:=hRef1) (hεref:=he.le)
    (hεrefhalf:=hehalf) (hηref:=he) (hχrefeq:=rfl) (hεrefeq:=rfl)
    (hηrefeq:=rfl) (p:=p) (hp:=hp) (Bcur:=fun i k=>B i (p*(k+3)))
    (Bword:=fun i k=>B i (k+3)) (Bref:=fun i k=>B i ((2*p)*(k+3))) (Berror:=fun i k=>B i (k+2)) (horder:=horder)
    (horderref:=horderref) (htail:=htail) (ηmark:=D.beta/100) (hηmark:=he)
    (hηmarkβ:=heβ) (ηleaf:=D.beta/100) (hηleaf:=he) (hηleafβ:=hLeaf)
    (leafOrder:=2) (hleafOrder:=by omega) (hoLeaf0:=ho0) (hoLeaf1:=ho1)
    (hdepth:=by dsimp only [N];omega) (BI0:=BI0) (BI1:=BI1) (B16:=fun i=>B i 8)
    (Bpast:=fun i=>B i 2) (Bnext:=Bnext) (B4:=fun i=>B i 4) (B8:=fun i=>B i 8)
    (B1:=fun i=>B i 1) (Bleaf:=fun i=>B i (2*((N+1)+2))) (Bcov:=fun i=>B i (N+3)) (hBI0:=hBI0)
    (hBI1:=hBI1) (hB16:=hB16) (hBDGpast:=fun i=>hBDG i 2 (by omega)) (hBDGnext:=hBDGnext)
    (hBDG4:=fun i=>hBDG i 4 (by omega)) (hBDG8:=fun i=>hBDG i 8 (by omega)) (hBDG1:=fun i=>hBDG i 1 (by omega)) (hBDGcur:=fun i k _=>hBDG i (p*(k+3)) (Nat.mul_pos hp (by omega)))
    (hBDGword:=fun i k _=>hBDG i (k+3) (by omega)) (hBDGref:=fun i k _=>hBDG i ((2*p)*(k+3)) (Nat.mul_pos (by omega) (by omega))) (hBDGerror:=fun i k _=>hBDG i (k+2) (by omega)) (hBDGleaf:=fun i=>hBDG i (2*((N+1)+2)) (by omega))
    (hBDGcov:=fun i=>hBDG i (N+3) (by omega)) (hqh:=hqh) (hbad:=hbad) (hqr:=hqr)
    (hHpos:=hHor) (hH:=hHreal) (hsmallProfile:=fun n=>(hsmall n).1) (hsmallL2:=fun n=>(hsmall n).2)
    (hcut:=hcut) (hfreq:=hfreq) (hlow:=hlow) (U:=U)
  exact ⟨Λ,hΛ1,hΛ,SS,hSS,index,hi,hit,hcost⟩
end SHE.GivenCanonicalCostLimit
