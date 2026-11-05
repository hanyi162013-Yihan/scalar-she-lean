module

public import SHE.NativeFixedHaarInput
public import SHE.SingularStoppedVersion
public import SHE.PredictableScalarField
public import SHE.PredictablePastParameter
public import SHE.PastItoInputs

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1700000
namespace SHE.NativeFrozenHilbertField
open Set MeasureTheory PredictableL2 FiniteHaar NativeHeatObservation DyadicApproximation
open scoped NNReal ENNReal
local instance nativeFrozenHilbertField_period : Fact (0<2*Real.pi):=⟨by positivity⟩
local instance nativeFrozenHilbertField_unit : Fact (0<(1:ℝ)):=⟨zero_lt_one⟩
local instance nativeFrozenHilbertField_circleSecond : SecondCountableTopology CircleHeat.CircleL2:=
  (_root_.fourierBasis (T:=(1:ℝ))).repr.toHomeomorph.secondCountableTopology
local instance nativeFrozenHilbertField_realSecond : SecondCountableTopology RealL2:=
  realCircleIdentification.toHomeomorph.secondCountableTopology
local instance nativeFrozenHilbertField_realSigma : MeasurableSpace RealL2:=borel _
local instance nativeFrozenHilbertField_realBorel : BorelSpace RealL2:=⟨rfl⟩
local instance nativeFrozenHilbertField_unitSigma : MeasurableSpace CircleHeat.CircleL2:=borel _
local instance nativeFrozenHilbertField_unitBorel : BorelSpace CircleHeat.CircleL2:=⟨rfl⟩
local instance nativeFrozenHilbertField_columnsSigma : MeasurableSpace RealHaarIntegrand.Columns:=borel _
local instance nativeFrozenHilbertField_columnsBorel : BorelSpace RealHaarIntegrand.Columns:=⟨rfl⟩
variable {Ω : Type*} [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H b v : ℝ≥0)
variable {ell M : ℝ} (hell : 0<ell) (hM : 0≤M)
variable (f : ℝ≥0×Ω→EllipticField ell M) (hf : StronglyMeasurable[𝓕.predictable] f)
variable (hbH : b≤H) (hb1 : (b:ℝ)≤1)

/-- The literal full-target native kernel on the SAME full-H noise,
with only its post-v support retained. -/
def input : Process (E:=RealHaarIntegrand.Columns) 𝓕 μ H:=
  PastItoInputs.post 𝓕 μ H v (NativeFixedHaarInput.input 𝓕 μ H hell hM f hf b hbH hb1)

theorem singular_cap : ∀ᵐ p∂energyMeasure μ H,p.1≤b→‖input 𝓕 μ H b v hell hM f hf hbH hb1 p‖^2≤
    FixedTargetKernelBound.constant M*((b:ℝ)-(p.1:ℝ))^(-(1/2:ℝ)) := by
  filter_upwards [PastItoInputs.post_ae 𝓕 μ H v (NativeFixedHaarInput.input 𝓕 μ H hell hM f hf b hbH hb1),
    NativeFixedHaarInput.singular_cap 𝓕 μ H hell hM f hf b hbH hb1] with p hp hcap hpb
  change ‖PastItoInputs.post 𝓕 μ H v (NativeFixedHaarInput.input 𝓕 μ H hell hM f hf b hbH hb1) p‖^2≤_
  rw [hp]
  split_ifs
  · exact hcap hpb
  · simp only [norm_zero,zero_pow (by norm_num : (2:ℕ)≠0)]
    exact mul_nonneg (FixedTargetKernelBound.constant_nonneg hM)
      (Real.rpow_nonneg (sub_nonneg.mpr (by exact_mod_cast hpb)) _)

variable (I : StandardTerminalIto (C:=RealHaarIntegrand.Columns) (E:=RealL2) 𝓕 μ H)

def noise (t : ℝ≥0) (ω : Ω) : RealL2:=
  SingularStoppedVersion.version 𝓕 μ H b I (input 𝓕 μ H b v hell hM f hf hbH hb1) t ω

theorem noise_continuous (hb0 : 0<b) (ω : Ω) :
    Continuous (fun t=>noise 𝓕 μ H b v hell hM f hf hbH hb1 I t ω):=
  SingularStoppedVersion.continuous_version 𝓕 μ H b I _ hb0 ω

theorem noise_ae (hb0 : 0<b) (B : ℝ≥0) (hBDG : StandardTerminalBDG16 I B)
    (t : ℝ≥0) (ht : t≤b) :
    noise 𝓕 μ H b v hell hM f hf hbH hb1 I t=ᵐ[μ]
      I.integral (StoppedItoInputs.stop 𝓕 μ H (t:ℝ) (input 𝓕 μ H b v hell hM f hf hbH hb1)) := by
  have he:=SingularStoppedVersion.version_ae 𝓕 μ H b I (input 𝓕 μ H b v hell hM f hf hbH hb1)
    hbH hb0 B hBDG (FixedTargetKernelBound.constant_nonneg hM)
    (singular_cap 𝓕 μ H b v hell hM f hf hbH hb1) t
  unfold noise
  simpa only [min_eq_left (show (t:ℝ)≤(b:ℝ) by exact_mod_cast ht)] using he

theorem noise_predictable (hb0 : 0<b) (hnull : NullCompleteFiltration.ContainsNullSets 𝓕 μ)
    (B : ℝ≥0) (hBDG : StandardTerminalBDG16 I B) :
    StronglyMeasurable[𝓕.predictable] (Function.uncurry (noise 𝓕 μ H b v hell hM f hf hbH hb1 I)) :=
  SingularStoppedVersion.predictable_version 𝓕 μ H b I (input 𝓕 μ H b v hell hM f hf hbH hb1)
    hbH hb0 hnull B hBDG (FixedTargetKernelBound.constant_nonneg hM)
    (singular_cap 𝓕 μ H b v hell hM f hf hbH hb1)

/-- An arbitrary genuine F_v-past initial full-target field is made
predictably available strictly after v. It is never declared adapted
before that past time. -/
def field (Z : Ω→RealL2) (p : ℝ≥0×Ω) : RealL2:=
  PredictablePastParameter.held v Z 0 p+noise 𝓕 μ H b v hell hM f hf hbH hb1 I p.1 p.2

theorem field_predictable (hb0 : 0<b) (hnull : NullCompleteFiltration.ContainsNullSets 𝓕 μ)
    (B : ℝ≥0) (hBDG : StandardTerminalBDG16 I B) (Z : Ω→RealL2) (hZ : Measurable[𝓕 v] Z) :
    StronglyMeasurable[𝓕.predictable] (field 𝓕 μ H b v hell hM f hf hbH hb1 I Z) :=
  ((PredictablePastParameter.held_measurable 𝓕 v Z hZ 0).stronglyMeasurable).add
    (noise_predictable 𝓕 μ H b v hell hM f hf hbH hb1 I hb0 hnull B hBDG)

theorem field_ae (hb0 : 0<b) (B : ℝ≥0) (hBDG : StandardTerminalBDG16 I B)
    (Z : Ω→RealL2) (t : ℝ≥0) (hvt : v<t) (htb : t≤b) :
    (fun ω=>field 𝓕 μ H b v hell hM f hf hbH hb1 I Z (t,ω))=ᵐ[μ]
      (fun ω=>Z ω+I.integral (StoppedItoInputs.stop 𝓕 μ H (t:ℝ)
        (input 𝓕 μ H b v hell hM f hf hbH hb1)) ω) := by
  filter_upwards [noise_ae 𝓕 μ H b v hell hM f hf hbH hb1 I hb0 B hBDG t htb] with ω hω
  rw [field,PredictablePastParameter.held_eq Z 0 hvt,hω]

/-- Actual jointly predictable scalar physical reference field, rather
than a separately selected version for each spatial observation. -/
theorem scalar_predictable (hb0 : 0<b) (hnull : NullCompleteFiltration.ContainsNullSets 𝓕 μ)
    (B : ℝ≥0) (hBDG : StandardTerminalBDG16 I B) (Z : Ω→RealL2) (hZ : Measurable[𝓕 v] Z) :
    @Measurable ((ℝ≥0×Ω)×StoppedFourier.HeatCircle) ℝ
      (𝓕.predictable.prod inferInstance) _
      (PredictableScalarField.nativeField (field 𝓕 μ H b v hell hM f hf hbH hb1 I Z)) :=
  PredictableScalarField.nativeField_predictable 𝓕
    (field_predictable 𝓕 μ H b v hell hM f hf hbH hb1 I hb0 hnull B hBDG Z hZ)

end SHE.NativeFrozenHilbertField
