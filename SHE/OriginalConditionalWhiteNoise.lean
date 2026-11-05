module
public import SHE.AllHorizonStatePrefixBrownian
public import SHE.CanonicalConditionalItoConstruction
public import SHE.CanonicalStateDriverPredictable
public import SHE.NativeSingleNoiseBasis
public import SHE.DeterministicItoShiftCoordinates
public import SHE.CanonicalScalarItoCells
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 2200000
namespace SHE.OriginalConditionalWhiteNoise
open MeasureTheory ProbabilityTheory PredictableL2 Set FiniteHaar
open scoped NNReal ENNReal
local instance : MeasurableSpace RealHaarInput := borel _
local instance : BorelSpace RealHaarInput := ⟨rfl⟩
variable {Ω E:Type*} [MeasurableSpace Ω]
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
variable (𝓕:Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ:Measure Ω) [IsProbabilityMeasure μ] (H:ℝ≥0)
variable (U:ℝ≥0→Ω→E) (hc:∀ω,Continuous (fun t=>U t ω))
variable (hU:∀t,Measurable[𝓕 t] (U t))
variable (J:StandardTerminalIto (C:=RealHaarInput) (E:=ℝ) 𝓕 μ H)
variable (B:ℝ≥0) (hBDG:StandardTerminalBDG16 J B) (hpos:0<H)
variable (hnull:NullCompleteFiltration.ContainsNullSets 𝓕 μ) (hLevy:StandardTerminalLevy J)

def globalDriver : HaarNode→ℝ≥0→Ω→ℝ :=
  RawCylindricalCoordinates.continuous 𝓕 μ H NativeSingleNoiseBasis.basis J

include hpos in
theorem global_continuous (i:HaarNode) (ω:Ω):
    Continuous (fun t=>globalDriver 𝓕 μ H J i t ω) :=
  BoundedStoppedVersion.continuous_version 𝓕 μ H J
    (RawCylindricalCoordinates.row 𝓕 μ H NativeSingleNoiseBasis.basis i) hpos ω

include hBDG hpos hnull in
theorem global_predictable (i:HaarNode):
    IsStronglyPredictable 𝓕 (globalDriver 𝓕 μ H J i) :=
  AllHorizonStoppedVersion.predictable_version 𝓕 μ H J
    (RawCylindricalCoordinates.row 𝓕 μ H NativeSingleNoiseBasis.basis i)
    hpos hnull B hBDG (by norm_num : 0≤(1:ℝ))
    (RawCylindricalCoordinates.row_norm 𝓕 μ H NativeSingleNoiseBasis.basis
      NativeSingleNoiseBasis.basis.orthonormal i)

include hBDG hpos hnull in
theorem global_adapted (i:HaarNode) (t:ℝ≥0):
    Measurable[𝓕 t] (globalDriver 𝓕 μ H J i t) :=
  ((global_predictable 𝓕 μ H J B hBDG hpos hnull i).stronglyAdapted t).measurable

include hBDG hpos hnull in
theorem global_joint_measurable (i:HaarNode):
    Measurable (Function.uncurry (globalDriver 𝓕 μ H J i)) :=
  ((global_predictable 𝓕 μ H J B hBDG hpos hnull i).mono (predictable_le_product 𝓕)).measurable

def shiftedState (v:ℝ≥0) (t:ℝ≥0) (ω:Ω):E := U (v+t) ω

include hc in
theorem state_continuous (v:ℝ≥0) (ω:Ω):
    Continuous (fun t=>shiftedState U v t ω) :=
  (hc ω).comp (continuous_const.add continuous_id)

def shiftedDriver (v:ℝ≥0) (i:HaarNode) (t:ℝ≥0) (ω:Ω):ℝ :=
  globalDriver 𝓕 μ H J i (v+t) ω-globalDriver 𝓕 μ H J i v ω

include hpos in
theorem driver_continuous (v:ℝ≥0) (i:HaarNode) (ω:Ω):
    Continuous (fun t=>shiftedDriver 𝓕 μ H J v i t ω) :=
  ((global_continuous 𝓕 μ H J hpos i ω).comp (continuous_const.add continuous_id)).sub continuous_const

include hU hc in
theorem state_predictable (v:ℝ≥0):
    IsStronglyPredictable (DeterministicItoShift.filtration 𝓕 v) (shiftedState U v) :=
  ContinuousPredictable.isStronglyPredictable _ _
    (fun t=>(hU (v+t)).stronglyMeasurable) (state_continuous U hc v)

include hBDG hpos hnull in
theorem driver_predictable (v:ℝ≥0) (i:HaarNode):
    IsStronglyPredictable (DeterministicItoShift.filtration 𝓕 v) (shiftedDriver 𝓕 μ H J v i) :=by
  apply ContinuousPredictable.isStronglyPredictable _ _ _ (driver_continuous 𝓕 μ H J hpos v i)
  intro t
  exact ((global_adapted 𝓕 μ H J B hBDG hpos hnull i (v+t)).sub
    ((global_adapted 𝓕 μ H J B hBDG hpos hnull i v).mono
      (𝓕.mono (le_add_of_nonneg_right t.2)) le_rfl)).stronglyMeasurable

include hU hc in
theorem state_joint_measurable (v:ℝ≥0):
    Measurable (Function.uncurry (shiftedState U v)) :=
  ((state_predictable 𝓕 U hc hU v).mono (predictable_le_product _)).measurable

include hBDG hpos hnull in
theorem driver_joint_measurable (v:ℝ≥0) (i:HaarNode):
    Measurable (Function.uncurry (shiftedDriver 𝓕 μ H J v i)) :=
  ((driver_predictable 𝓕 μ H J B hBDG hpos hnull v i).mono (predictable_le_product _)).measurable

def bundle (v h:ℝ≥0):Ω→CanonicalContinuousStateDriver.Space (E:=E) (ι:=HaarNode) h :=
  CanonicalContinuousStateDriver.bundle h (shiftedState U v) (state_continuous U hc v)
    (shiftedDriver 𝓕 μ H J v) (driver_continuous 𝓕 μ H J hpos v)

theorem bundle_eq (v h:ℝ≥0):
    bundle 𝓕 μ H U hc J hpos v h =
      AllHorizonOriginalConditionalBrownian.bundle 𝓕 μ H U hc NativeSingleNoiseBasis.basis J hpos v h :=by
  funext ω
  apply Prod.ext
  · apply ContinuousMap.ext
    intro t
    rfl
  · funext i
    apply ContinuousMap.ext
    intro t
    rfl

include hU hBDG hpos hnull in
theorem bundle_measurable (v h:ℝ≥0): Measurable (bundle 𝓕 μ H U hc J hpos v h) :=
  CanonicalContinuousStateDriver.measurable_bundle h _ _ _ _
    (state_joint_measurable 𝓕 U hc hU v) (driver_joint_measurable 𝓕 μ H J B hBDG hpos hnull v)

include hBDG hpos in
theorem shifted_coordinate (v h:ℝ≥0) (hvh:v+h≤H) (i:HaarNode) (t:ℝ≥0) (ht:t≤h):
    shiftedDriver 𝓕 μ H J v i t =ᵐ[μ]
      RawCylindricalCoordinates.value (DeterministicItoShift.filtration 𝓕 v) μ h
        NativeSingleNoiseBasis.basis (DeterministicItoShift.integral 𝓕 μ H v h hvh J) i t :=
  DeterministicItoShiftCoordinates.continuous_ae 𝓕 μ H v h hvh NativeSingleNoiseBasis.basis J
    NativeSingleNoiseBasis.basis.orthonormal B hBDG hpos i t ht

include hBDG hpos in
theorem shifted_white_coordinate (v h:ℝ≥0) (hvh:v+h≤H) (i:HaarNode) (t:ℝ≥0) (ht:t≤h):
    shiftedDriver 𝓕 μ H J v i t =ᵐ[μ]
      CanonicalScalarItoCells.coordinate h i (DeterministicItoShift.filtration 𝓕 v) μ
        (DeterministicItoShift.integral 𝓕 μ H v h hvh J) t :=by
  filter_upwards [shifted_coordinate 𝓕 μ H J B hBDG hpos v h hvh i t ht] with ω hω
  apply hω.trans
  unfold RawCylindricalCoordinates.value RawCylindricalCoordinates.row CanonicalScalarItoCells.coordinate
  rw [NativeSingleNoiseBasis.basis_apply]

include hU hBDG hpos hnull hLevy in
/-- The actual original white driver supplies a conditional integral on
one state-prefix event. Every coordinate belongs to the SAME original
shifted integral; the only construction premise is ordinary package1. -/
theorem exists_integral (v h:ℝ≥0) (hvh:v+h≤H)
    (hConstruct:∀p,StandardBrownianItoConstruction
      (CanonicalStateDriverFiltration.filtration (E:=E) (ι:=HaarNode) h)
      (condDistrib (bundle 𝓕 μ H U hc J hpos v h) (NativeContinuousPath.path v U hc) μ p)
      h NativeSingleNoiseBasis.basis (CanonicalStateDriverFiltration.coordinate h)):
    ∀ᵐp∂μ.map (NativeContinuousPath.path v U hc),
      ∃K:StandardTerminalIto (C:=RealHaarInput) (E:=ℝ)
        (CanonicalStateDriverFiltration.filtration (E:=E) (ι:=HaarNode) h)
        (condDistrib (bundle 𝓕 μ H U hc J hpos v h) (NativeContinuousPath.path v U hc) μ p) h,
      StandardTerminalPastLocality K ∧ StandardHilbertItoLift K ∧
      ∀i (t:ℝ≥0),t≤h→
        (K.integral (StoppedItoInputs.stop _ _ _ t
          (RawCylindricalCoordinates.row _ _ _ (NativeSingleNoiseBasis.basis:HaarNode→RealHaarInput) i)))=ᵐ[
            condDistrib (bundle 𝓕 μ H U hc J hpos v h) (NativeContinuousPath.path v U hc) μ p]
          CanonicalStateDriverFiltration.coordinate h i t :=by
  have hb:=AllHorizonStatePrefixBrownian.law 𝓕 μ H U hc hU NativeSingleNoiseBasis.basis
    NativeSingleNoiseBasis.basis.orthonormal J B hBDG hpos hnull hLevy v h hvh
  rw[←bundle_eq 𝓕 μ H U hc J hpos v h] at hb
  filter_upwards[hb] with p hp
  exact hConstruct p (fun i r=>CanonicalStateDriverFiltration.coordinate_continuous h i r)
    (fun i t=>CanonicalStateDriverFiltration.coordinate_adapted h i t) hp
end SHE.OriginalConditionalWhiteNoise
