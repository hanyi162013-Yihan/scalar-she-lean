module
public import SHE.GivenSplitNativeLocalUniqueness
public import SHE.OriginalNativeSplitMild
public import SHE.PredictableScalarHaarInputs
public import SHE.RotatedStoppedFubini
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
set_option quotPrecheck false
namespace SHE.GivenOriginalNativeLocalUniqueness
open MeasureTheory PredictableL2 NativeHeatObservation NativeObservationNaturality
open FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation
open scoped NNReal ENNReal
local instance : Fact (0<(1:ℝ)):=⟨zero_lt_one⟩
local instance : Fact (0<2*Real.pi):=⟨by positivity⟩
local instance : Fact ((2:ENNReal)≠⊤):=⟨by simp⟩
local instance : SecondCountableTopology CircleHeat.CircleL2:=
  (_root_.fourierBasis (T:=1)).repr.toHomeomorph.secondCountableTopology
local instance : SecondCountableTopology RealL2:=realCircleIdentification.toHomeomorph.secondCountableTopology
local instance : MeasurableSpace RealL2:=borel _
local instance : BorelSpace RealL2:=⟨rfl⟩
local instance : MeasurableSpace CircleHeat.CircleL2:=borel _
local instance : BorelSpace CircleHeat.CircleL2:=⟨rfl⟩
local instance : MeasurableSpace RealHaarInput:=borel _
local instance : BorelSpace RealHaarInput:=⟨rfl⟩
local instance : MeasurableSpace (Both RealHaarInput):=borel _
local instance : BorelSpace (Both RealHaarInput):=⟨rfl⟩
local instance : MeasurableSpace RealHaarIntegrand.Columns:=borel _
local instance : BorelSpace RealHaarIntegrand.Columns:=⟨rfl⟩
variable {ι:Type}[Fintype ι](Ω:ι→Type)[∀i,MeasurableSpace (Ω i)]
variable (𝓕:∀i,Filtration ℝ≥0 (inferInstance:MeasurableSpace (Ω i)))
  (μ:∀i,Measure (Ω i))[∀i,IsProbabilityMeasure (μ i)]
variable (h:ℝ≥0)(hh:(h:ℝ)≤1)(hpos:0<h)(hNative:(NativeClock.rate*h:ℝ≥0)≤1)
  (D:SmoothApproximation.ScalarData)
variable (Bphysical:∀i,StandardTerminalIto (C:=Both RealL2) (E:=ℝ) (PredictableTimeDilation.filtration (𝓕 i) (PredictableTimeDilation.clock NativeClock.rate NativeClock.rate_pos)) (μ i) (NativeClock.rate*h))
variable (u₀:RealL2)
variable (U:∀i,OriginalNativeHeatEquation.Data (PredictableTimeDilation.filtration (𝓕 i) (PredictableTimeDilation.clock NativeClock.rate NativeClock.rate_pos)) (μ i) (NativeClock.rate*h) D (Bphysical i) u₀)

/-- The actual Haar driver is fixed by the original supplied path and
original augmented physical noise. It is never chosen independently. -/
def driver(i:ι):StandardTerminalIto (C:=Both RealHaarInput) (E:=ℝ) (PredictableTimeDilation.filtration (𝓕 i) (PredictableTimeDilation.clock NativeClock.rate NativeClock.rate_pos)) (μ i) (NativeClock.rate*h):=
  PredictableScalarHaarRotation.integral (PredictableTimeDilation.filtration (𝓕 i) (PredictableTimeDilation.clock NativeClock.rate NativeClock.rate_pos)) (μ i) (NativeClock.rate*h) D
    (Function.uncurry (U i).value) (U i).predictable (Bphysical i)

variable (I₀ I₁:∀i,StandardTerminalIto (C:=RealHaarIntegrand.Columns) (E:=RealL2) (PredictableTimeDilation.filtration (𝓕 i) (PredictableTimeDilation.clock NativeClock.rate NativeClock.rate_pos)) (μ i) (NativeClock.rate*h))
variable (hIJ₀:∀i,StandardScalarNaturality (I₀ i) (leftIntegral (PredictableTimeDilation.filtration (𝓕 i) (PredictableTimeDilation.clock NativeClock.rate NativeClock.rate_pos)) (μ i) (NativeClock.rate*h) (driver (Ω:=Ω) (𝓕:=𝓕) (μ:=μ) (h:=h) (D:=D) (Bphysical:=Bphysical) (u₀:=u₀) (U:=U) i)))
  (hIJ₁:∀i,StandardScalarNaturality (I₁ i) (rightIntegral (PredictableTimeDilation.filtration (𝓕 i) (PredictableTimeDilation.clock NativeClock.rate NativeClock.rate_pos)) (μ i) (NativeClock.rate*h) (driver (Ω:=Ω) (𝓕:=𝓕) (μ:=μ) (h:=h) (D:=D) (Bphysical:=Bphysical) (u₀:=u₀) (U:=U) i)))

include hIJ₀ hIJ₁ in
/-- Clock recasting of the derived split model retains the original path
pointwise, with no assumed split mild equation. -/
def split(i:ι):NativeFirstMildData.Data (𝓕 i) (μ i) h ((ScalarReduction.additiveAmplitude D.lower)^2) (CanonicalFixedHorizonCompanions.additive_pos D)
    D.residual_continuous.measurable D.ell_pos D.residual_bounds (I₀ i) (I₁ i) u₀:=by
  let S:=OriginalNativeSplitMild.of_original (PredictableTimeDilation.filtration (𝓕 i) (PredictableTimeDilation.clock NativeClock.rate NativeClock.rate_pos)) (μ i) (NativeClock.rate*h) D (Bphysical i) u₀ (U i)
    (show ((NativeClock.rate*h):ℝ)≤1 by exact_mod_cast hNative) (I₀ i) (I₁ i) (hIJ₀ i) (hIJ₁ i)
  exact {
    value:=S.value
    continuous:=S.continuous
    predictable:=S.predictable
    coefficient:=S.coefficient
    additiveInput:=S.additiveInput
    residualInput:=S.residualInput
    additive_kernel:=S.additive_kernel
    residual_kernel:=S.residual_kernel
    mild:=S.mild }


variable (hnull:∀i,NullCompleteFiltration.ContainsNullSets (PredictableTimeDilation.filtration (𝓕 i) (PredictableTimeDilation.clock NativeClock.rate NativeClock.rate_pos)) (μ i))
  (hJ:∀i,StandardFiniteIto.Universal (PredictableTimeDilation.filtration (𝓕 i) (PredictableTimeDilation.clock NativeClock.rate NativeClock.rate_pos)) (μ i) (NativeClock.rate*h) (driver (Ω:=Ω) (𝓕:=𝓕) (μ:=μ) (h:=h) (D:=D) (Bphysical:=Bphysical) (u₀:=u₀) (U:=U) i))
  (hlocal:∀i,StandardTerminalPastLocality (driver (Ω:=Ω) (𝓕:=𝓕) (μ:=μ) (h:=h) (D:=D) (Bphysical:=Bphysical) (u₀:=u₀) (U:=U) i))(hlocalI:∀i,StandardTerminalPastLocality (I₁ i))
  (hFstop:∀i,StandardItoStoppedParameterFubini (driver (Ω:=Ω) (𝓕:=𝓕) (μ:=μ) (h:=h) (D:=D) (Bphysical:=Bphysical) (u₀:=u₀) (U:=U) i))
variable (BI0 BI1 Bnext:ι→ℝ≥0)(B:ι→ℕ→ℝ≥0)
  (hBI0:∀i,StandardTerminalBDG16 (I₀ i) (BI0 i))(hBI1:∀i,StandardTerminalBDG16 (I₁ i) (BI1 i))
  (hBDGnext:∀i,StandardTerminalBDGPower 1 (I₁ i) (Bnext i))
  (hBDG:∀i p,0<p→StandardTerminalBDGPower p (driver (Ω:=Ω) (𝓕:=𝓕) (μ:=μ) (h:=h) (D:=D) (Bphysical:=Bphysical) (u₀:=u₀) (U:=U) i) (B i p))
variable (hNovikov:∀i,StandardTerminalNovikov (driver (Ω:=Ω) (𝓕:=𝓕) (μ:=μ) (h:=h) (D:=D) (Bphysical:=Bphysical) (u₀:=u₀) (U:=U) i))
  (hGirsanov:∀i,StandardTerminalGirsanov (driver (Ω:=Ω) (𝓕:=𝓕) (μ:=μ) (h:=h) (D:=D) (Bphysical:=Bphysical) (u₀:=u₀) (U:=U) i))
  (hRecognizedBDG:∀i,StandardChangedHilbertBDG
    (PredictableTimeDilation.filtration (𝓕 i) (PredictableTimeDilation.clock NativeClock.rate NativeClock.rate_pos))
    (μ i) (NativeClock.rate*h)
    (driver (Ω:=Ω) (𝓕:=𝓕) (μ:=μ) (h:=h) (D:=D) (Bphysical:=Bphysical) (u₀:=u₀) (U:=U) i))

include hh hpos hNative hIJ₀ hIJ₁ hnull hJ hlocal hlocalI hFstop hBI0 hBI1 hBDGnext hBDG
  hNovikov hGirsanov hRecognizedBDG in
/-- Local uniqueness for the GIVEN original observable equations on
arbitrary probability spaces. Their split mild models are constructed
internally under the exact solution-dependent rotated noise. The only
remaining hypotheses are ordinary stochastic packages on that noise. -/
theorem laws_eq:
    ∀i j:ι,NativePathLawComparison.law (NativeClock.rate*h) (μ i) (U i).value (U i).continuous=
      NativePathLawComparison.law (NativeClock.rate*h) (μ j) (U j).value (U j).continuous:=by
  let S:=split (Ω:=Ω) (𝓕:=𝓕) (μ:=μ) (h:=h) (hNative:=hNative) (D:=D)
    (Bphysical:=Bphysical) (u₀:=u₀) (U:=U) (I₀:=I₀) (I₁:=I₁) (hIJ₀:=hIJ₀) (hIJ₁:=hIJ₁)
  exact GivenSplitNativeLocalUniqueness.laws_eq Ω 𝓕 μ h hh hpos hNative D I₀ I₁ (driver (Ω:=Ω) (𝓕:=𝓕) (μ:=μ) (h:=h) (D:=D) (Bphysical:=Bphysical) (u₀:=u₀) (U:=U))
    hIJ₀ hIJ₁ hnull hJ hlocal hlocalI hFstop BI0 BI1 Bnext B hBI0 hBI1 hBDGnext hBDG
    u₀ S hNovikov hGirsanov hRecognizedBDG

include hh hpos hNative hIJ₀ hIJ₁ hnull hBI0 hBI1 hBDGnext hGirsanov hRecognizedBDG in
/-- The ordinary finite Ito, locality, Fubini, Novikov and all-order BDG
hypotheses can be placed on the original augmented physical noise.
Their applicability to the actual split driver is derived internally. -/
theorem laws_eq_of_physical
    (hOriginalFiniteIto:∀i,StandardFiniteIto.Universal (PredictableTimeDilation.filtration (𝓕 i) (PredictableTimeDilation.clock NativeClock.rate NativeClock.rate_pos)) (μ i) (NativeClock.rate*h) (Bphysical i))
    (hOriginalLocality:∀i,StandardTerminalPastLocality (Bphysical i))
    (hOriginalFubini:∀i,StandardItoStoppedParameterFubini (Bphysical i))
    (hOriginalNovikov:∀i,StandardTerminalNovikov (Bphysical i))
    (hOriginalBDG:∀i p,0<p→StandardTerminalBDGPower p (Bphysical i) (B i p)):
    ∀i j:ι,NativePathLawComparison.law (NativeClock.rate*h) (μ i) (U i).value (U i).continuous=
      NativePathLawComparison.law (NativeClock.rate*h) (μ j) (U j).value (U j).continuous:=by
  have hFin(i:ι):StandardFiniteIto.Universal (PredictableTimeDilation.filtration (𝓕 i) (PredictableTimeDilation.clock NativeClock.rate NativeClock.rate_pos)) (μ i) (NativeClock.rate*h) (driver (Ω:=Ω) (𝓕:=𝓕) (μ:=μ) (h:=h) (D:=D) (Bphysical:=Bphysical) (u₀:=u₀) (U:=U) i):=
    PredictableScalarHaarRotation.finiteIto (PredictableTimeDilation.filtration (𝓕 i) (PredictableTimeDilation.clock NativeClock.rate NativeClock.rate_pos)) (μ i) (NativeClock.rate*h) D
      (Function.uncurry (U i).value) (U i).predictable (Bphysical i) (hOriginalFiniteIto i)
  have hLoc(i:ι):StandardTerminalPastLocality (driver (Ω:=Ω) (𝓕:=𝓕) (μ:=μ) (h:=h) (D:=D) (Bphysical:=Bphysical) (u₀:=u₀) (U:=U) i):=
    PredictableScalarHaarRotation.locality (PredictableTimeDilation.filtration (𝓕 i) (PredictableTimeDilation.clock NativeClock.rate NativeClock.rate_pos)) (μ i) (NativeClock.rate*h) D
      (Function.uncurry (U i).value) (U i).predictable (Bphysical i) (hOriginalLocality i)
  have hFub(i:ι):StandardItoStoppedParameterFubini (driver (Ω:=Ω) (𝓕:=𝓕) (μ:=μ) (h:=h) (D:=D) (Bphysical:=Bphysical) (u₀:=u₀) (U:=U) i):=
    PredictableScalarHaarRotation.stoppedFubini
      (PredictableTimeDilation.filtration (𝓕 i) (PredictableTimeDilation.clock NativeClock.rate NativeClock.rate_pos))
      (μ i) (NativeClock.rate*h) D (Function.uncurry (U i).value) (U i).predictable
      (Bphysical i) (hOriginalFubini i)
  have hNov(i:ι):StandardTerminalNovikov (driver (Ω:=Ω) (𝓕:=𝓕) (μ:=μ) (h:=h) (D:=D) (Bphysical:=Bphysical) (u₀:=u₀) (U:=U) i):=
    PredictableScalarHaarRotation.novikov (PredictableTimeDilation.filtration (𝓕 i) (PredictableTimeDilation.clock NativeClock.rate NativeClock.rate_pos)) (μ i) (NativeClock.rate*h) D
      (Function.uncurry (U i).value) (U i).predictable (Bphysical i) (hOriginalNovikov i)
  have hBd(i:ι)(p:ℕ)(hp:0<p):StandardTerminalBDGPower p (driver (Ω:=Ω) (𝓕:=𝓕) (μ:=μ) (h:=h) (D:=D) (Bphysical:=Bphysical) (u₀:=u₀) (U:=U) i) (B i p):=
    PredictableScalarHaarRotation.bdgPower (PredictableTimeDilation.filtration (𝓕 i) (PredictableTimeDilation.clock NativeClock.rate NativeClock.rate_pos)) (μ i) (NativeClock.rate*h) D
      (Function.uncurry (U i).value) (U i).predictable (Bphysical i) p (B i p) (hOriginalBDG i p hp)
  exact laws_eq (Ω:=Ω) (𝓕:=𝓕) (μ:=μ) (h:=h) (hh:=hh) (hpos:=hpos) (hNative:=hNative)
    (D:=D) (Bphysical:=Bphysical) (u₀:=u₀) (U:=U) (I₀:=I₀) (I₁:=I₁) (hIJ₀:=hIJ₀) (hIJ₁:=hIJ₁)
    (hnull:=hnull) (hJ:=hFin) (hlocal:=hLoc)
    (hlocalI:=fun i=>NativeHilbertPastLocality.right (PredictableTimeDilation.filtration (𝓕 i) (PredictableTimeDilation.clock NativeClock.rate NativeClock.rate_pos)) (μ i) (NativeClock.rate*h)
      (I₁ i) (driver (Ω:=Ω) (𝓕:=𝓕) (μ:=μ) (h:=h) (D:=D) (Bphysical:=Bphysical) (u₀:=u₀) (U:=U) i) (hIJ₁ i) (hLoc i))
    (hFstop:=hFub) (BI0:=BI0) (BI1:=BI1) (Bnext:=Bnext) (B:=B)
    (hBI0:=hBI0) (hBI1:=hBI1) (hBDGnext:=hBDGnext) (hBDG:=hBd)
    (hNovikov:=hNov) (hGirsanov:=hGirsanov) (hRecognizedBDG:=hRecognizedBDG)

end SHE.GivenOriginalNativeLocalUniqueness
