module
public import SHE.ConditionalSingleHeatModel
public import SHE.OriginalConditionalWhiteNoise
public import SHE.OriginalNativeWhiteDriver
public import SHE.DeterministicItoShiftLocality
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
namespace SHE.OriginalShiftedSingleModels
open MeasureTheory ProbabilityTheory Set PredictableL2 FiniteHaar DyadicApproximation OrthogonalItoChannels
open scoped NNReal ENNReal MeasureTheory ProbabilityTheory
local instance shiftedModels_unit:Fact (0<(1:ℝ)):=⟨zero_lt_one⟩
local instance shiftedModels_circleSecond:SecondCountableTopology CircleHeat.CircleL2:=
  (_root_.fourierBasis (T:=1)).repr.toHomeomorph.secondCountableTopology
local instance shiftedModels_realSecond:SecondCountableTopology RealL2:=
  realCircleIdentification.toHomeomorph.secondCountableTopology
local instance shiftedModels_realSigma:MeasurableSpace RealL2:=borel _
local instance shiftedModels_realBorel:BorelSpace RealL2:=⟨rfl⟩
local instance shiftedModels_rowSigma:MeasurableSpace RealHaarInput:=borel _
local instance shiftedModels_rowBorel:BorelSpace RealHaarInput:=⟨rfl⟩
local instance shiftedModels_bothSigma:MeasurableSpace (Both RealL2):=borel _
local instance shiftedModels_bothBorel:BorelSpace (Both RealL2):=⟨rfl⟩
variable {Ω:Type*}[MeasurableSpace Ω]
variable(𝓕:Filtration ℝ≥0 ‹MeasurableSpace Ω›)(μ:Measure Ω)[IsProbabilityMeasure μ](H:ℝ≥0)
variable(D:SmoothApproximation.ScalarData)(B:StandardTerminalIto (C:=Both RealL2) (E:=ℝ) 𝓕 μ H)
variable(u₀:RealL2)(S:OriginalNativeHeatEquation.Data 𝓕 μ H D B u₀)
variable(v h:ℝ≥0)(hvh:v+h≤H)

def source:RandomInitialSingleHeatEquation.Data (DeterministicItoShift.filtration 𝓕 v) μ h D
    (leftIntegral (DeterministicItoShift.filtration 𝓕 v) μ h (DeterministicItoShift.integral 𝓕 μ H v h hvh B))
    (S.value v):=
  RandomInitialSingleHeatEquation.of_original (DeterministicItoShift.filtration 𝓕 v) μ h D
    (DeterministicItoShift.integral 𝓕 μ H v h hvh B) (S.value v)
    (ShiftedOriginalNativeEquation.of_original 𝓕 μ H D B u₀ S v h hvh)

abbrev Prefix(v:ℝ≥0):=C(Icc (0:ℝ) (v:ℝ),RealL2)

def known(v:ℝ≥0)(p:Prefix v):RealL2:=p ⟨v,v.2,le_rfl⟩

theorem known_measurable(v:ℝ≥0):Measurable (known v):=ContinuousMap.measurable_eval _

variable(hpos:0<H)

def futureBundle:=OriginalConditionalWhiteNoise.bundle 𝓕 μ H S.value S.continuous
  (OriginalNativeWhiteDriver.integral 𝓕 μ H B) hpos v h

def kernel:Kernel (Prefix v) (ConditionalSingleHeatModel.Space h):=
  condDistrib (futureBundle 𝓕 μ H D B u₀ S v h hpos) (NativeContinuousPath.path v S.value S.continuous) μ

instance kernel_probability(p:Prefix v):IsProbabilityMeasure (kernel 𝓕 μ H D B u₀ S v h hpos p):=by
  unfold kernel
  infer_instance

include hvh in
/-- Actual restarted original equations, the SAME original white driver,
its state-prefix conditional Brownian construction, and the proved heat
transfer produce genuine conditional single-noise weak models. The
canonical state is retained exactly, and its initial state is the actual
prefix endpoint. No conditional SPDE or Markov premise is supplied. -/
theorem exists_models(C:ℝ≥0)(hBDG:StandardTerminalBDG16 B C)
    (hnull:NullCompleteFiltration.ContainsNullSets 𝓕 μ)(hLevy:StandardTerminalLevy B)
    (hlocal:StandardTerminalPastLocality B)
    (hConstruct:∀p,StandardBrownianItoConstruction
      (ConditionalSingleHeatModel.filtration h) (kernel 𝓕 μ H D B u₀ S v h hpos p)
      h NativeSingleNoiseBasis.basis (CanonicalStateDriverFiltration.coordinate h)):
    ∀ᵐp∂μ.map (NativeContinuousPath.path v S.value S.continuous),
      ∃K:StandardTerminalIto (C:=RealHaarInput) (E:=ℝ)
        (ConditionalSingleHeatModel.filtration h) (kernel 𝓕 μ H D B u₀ S v h hpos p) h,
      StandardTerminalPastLocality K ∧ StandardHilbertItoLift K ∧
      (∀i (t:ℝ≥0),t≤h→
        (K.integral (StoppedItoInputs.stop _ _ _ t
          (RawCylindricalCoordinates.row _ _ _ (NativeSingleNoiseBasis.basis:HaarNode→RealHaarInput) i)))=ᵐ[
            kernel 𝓕 μ H D B u₀ S v h hpos p] CanonicalStateDriverFiltration.coordinate h i t) ∧
      ∃R:SingleNativeHeatEquation.Data (ConditionalSingleHeatModel.filtration h)
        (kernel 𝓕 μ H D B u₀ S v h hpos p) h D
        (NativeWhiteToPhysicalEquation.physical (ConditionalSingleHeatModel.filtration h)
          (kernel 𝓕 μ H D B u₀ S v h hpos p) h K) (known v p),
        R.value=ConditionalSingleHeatModel.state h:=by
  let JW:=OriginalNativeWhiteDriver.integral 𝓕 μ H B
  have hBW:StandardTerminalBDG16 JW C:=OriginalNativeWhiteDriver.bdg 𝓕 μ H B C hBDG
  have hLW:StandardTerminalLevy JW:=OriginalNativeWhiteDriver.levy 𝓕 μ H B hLevy
  have hUa:∀t,Measurable[𝓕 t] (S.value t):=
    fun t=>(show IsStronglyPredictable 𝓕 S.value from S.predictable).stronglyAdapted t |>.measurable
  have hg:=OriginalConditionalWhiteNoise.exists_integral 𝓕 μ H S.value S.continuous hUa JW C hBW
    hpos hnull hLW v h hvh hConstruct
  let W:=OriginalConditionalWhiteNoise.shiftedDriver 𝓕 μ H JW v
  have hd:∀i ω,Continuous (fun t=>W i t ω):=
    OriginalConditionalWhiteNoise.driver_continuous 𝓕 μ H JW hpos v
  have hWm:∀i,Measurable (Function.uncurry (W i)):=
    OriginalConditionalWhiteNoise.driver_joint_measurable 𝓕 μ H JW C hBW hpos hnull v
  have hW:∀i t,t≤h→W i t=ᵐ[μ] CanonicalScalarItoCells.coordinate h i
      (DeterministicItoShift.filtration 𝓕 v) μ
      (OriginalSingleHaarInputs.integral (DeterministicItoShift.filtration 𝓕 v) μ h
        (leftIntegral (DeterministicItoShift.filtration 𝓕 v) μ h
          (DeterministicItoShift.integral 𝓕 μ H v h hvh B))) t:=by
    intro i t ht
    have hw:=OriginalConditionalWhiteNoise.shifted_white_coordinate 𝓕 μ H JW C hBW hpos v h hvh i t ht
    change W i t=ᵐ[μ] CanonicalScalarItoCells.coordinate h i
      (DeterministicItoShift.filtration 𝓕 v) μ
      (OriginalNativeWhiteDriver.integral (DeterministicItoShift.filtration 𝓕 v) μ h
        (DeterministicItoShift.integral 𝓕 μ H v h hvh B)) t
    rw [OriginalNativeWhiteDriver.shifted]
    exact hw
  have hk:Measurable (NativeContinuousPath.path v S.value S.continuous):=
    NativeContinuousPath.measurable_path v S.value S.continuous
      (S.predictable.mono (predictable_le_product 𝓕)).measurable
  have hknown:S.value v=ᵐ[μ] fun ω=>known v (NativeContinuousPath.path v S.value S.continuous ω):=by
    apply ae_of_all
    intro ω
    change S.value v ω=S.value (v:ℝ).toNNReal ω
    rw [Real.toNNReal_coe]
  have hshort:=OriginalNativeWhiteDriver.left_locality (DeterministicItoShift.filtration 𝓕 v) μ h
    (DeterministicItoShift.integral 𝓕 μ H v h hvh B)
    (DeterministicItoShift.locality 𝓕 μ H v h hvh B hlocal)
  have hm:=ConditionalSingleHeatModel.models (DeterministicItoShift.filtration 𝓕 v) μ h D
    (leftIntegral (DeterministicItoShift.filtration 𝓕 v) μ h
      (DeterministicItoShift.integral 𝓕 μ H v h hvh B)) (S.value v)
    (source 𝓕 μ H D B u₀ S v h hvh) W hd
    (NativeContinuousPath.path v S.value S.continuous) hk (known v) (known_measurable v) hknown hWm hshort hW
  filter_upwards [hg,hm] with p hp hm
  obtain ⟨K,hK,hLift,hBasis⟩:=hp
  obtain ⟨R,hR⟩:=hm K hK hBasis
  exact ⟨K,hK,hLift,hBasis,R,hR⟩
end SHE.OriginalShiftedSingleModels
