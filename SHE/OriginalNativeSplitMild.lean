module
public import SHE.OriginalNativeHeatEquation
public import SHE.NativeMildFirst
public import SHE.NativeFixedHaarInput
public import SHE.HeatObservationUniqueness
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
namespace SHE.OriginalNativeSplitMild
open Set MeasureTheory PredictableL2 NativeHeatObservation NativeObservationNaturality
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
local instance : MeasurableSpace RealHaarIntegrand.Columns:=borel _
local instance : BorelSpace RealHaarIntegrand.Columns:=⟨rfl⟩
variable {Ω:Type*}[MeasurableSpace Ω]
variable (𝓕:Filtration ℝ≥0 ‹MeasurableSpace Ω›)(μ:Measure Ω)[IsProbabilityMeasure μ](H:ℝ≥0)
variable (D:SmoothApproximation.ScalarData)
variable (B:StandardTerminalIto (C:=Both RealL2) (E:=ℝ) 𝓕 μ H)(u₀:RealL2)
variable (S:OriginalNativeHeatEquation.Data 𝓕 μ H D B u₀)(hH:(H:ℝ)≤1)
local notation "κ" => (ScalarHaarRotation.amplitude D)^2
local notation "hκ" => sq_pos_of_pos (ScalarHaarRotation.amplitude_pos D)
local notation "U" => Function.uncurry S.value
local notation "f0" => fun _:ℝ≥0×Ω=>AdditiveHaarForcing.constantField κ hκ
local notation "f1" => PredictableScalarHaarRotation.residual D U
local notation "hf1" => PredictableScalarHaarRotation.residual_predictable 𝓕 D U S.predictable
local notation "J" => PredictableScalarHaarRotation.integral 𝓕 μ H D U S.predictable B

def additiveInput(q:ℝ≥0):Process (E:=RealHaarIntegrand.Columns) 𝓕 μ H:=
  NativeFixedHaarInput.input 𝓕 μ H hκ (sq_nonneg _) f0 stronglyMeasurable_const (min q H)
    (min_le_right _ _) ((show ((min q H:ℝ≥0):ℝ)≤H by exact_mod_cast min_le_right q H).trans hH)

def residualInput(q:ℝ≥0):Process (E:=RealHaarIntegrand.Columns) 𝓕 μ H:=
  NativeFixedHaarInput.input 𝓕 μ H D.ell_pos D.cap_nonneg f1 hf1 (min q H)
    (min_le_right _ _) ((show ((min q H:ℝ≥0):ℝ)≤H by exact_mod_cast min_le_right q H).trans hH)

theorem additive_kernel(q:ℝ≥0)(hq:q≤H):
    additiveInput 𝓕 μ H D hH q=ᵐ[energyMeasure μ H]
      (fun p=>NativeHeatObservation.kernel κ κ hκ ((q:ℝ)-(p.1:ℝ),f0 p)):=by
  have hi:=NativeFixedHaarInput.input_ae 𝓕 μ H hκ (sq_nonneg _) f0
    stronglyMeasurable_const (min q H) (min_le_right _ _)
      ((show ((min q H:ℝ≥0):ℝ)≤H by exact_mod_cast min_le_right q H).trans hH)
  filter_upwards [hi] with p hp
  change additiveInput 𝓕 μ H D hH q p=_ at hp
  rw [hp]
  change NativeHeatObservation.kernel κ κ hκ (((min q H:ℝ≥0):ℝ)-(p.1:ℝ),f0 p)=_
  rw [min_eq_left hq]

theorem residual_kernel(q:ℝ≥0)(hq:q≤H):
    residualInput 𝓕 μ H D B u₀ S hH q=ᵐ[energyMeasure μ H]
      (fun p=>NativeHeatObservation.kernel D.ell D.cap D.ell_pos ((q:ℝ)-(p.1:ℝ),f1 p)):=by
  have hi:=NativeFixedHaarInput.input_ae 𝓕 μ H D.ell_pos D.cap_nonneg f1
    hf1 (min q H) (min_le_right _ _)
      ((show ((min q H:ℝ≥0):ℝ)≤H by exact_mod_cast min_le_right q H).trans hH)
  filter_upwards [hi] with p hp
  change residualInput 𝓕 μ H D B u₀ S hH q p=_ at hp
  rw [hp]
  change NativeHeatObservation.kernel D.ell D.cap D.ell_pos (((min q H:ℝ≥0):ℝ)-(p.1:ℝ),f1 p)=_
  rw [min_eq_left hq]

variable (I0 I1:StandardTerminalIto (C:=RealHaarIntegrand.Columns) (E:=RealL2) 𝓕 μ H)
variable (hI0:StandardScalarNaturality I0 (leftIntegral 𝓕 μ H
  (PredictableScalarHaarRotation.integral 𝓕 μ H D (Function.uncurry S.value) S.predictable B)))
variable (hI1:StandardScalarNaturality I1 (rightIntegral 𝓕 μ H
  (PredictableScalarHaarRotation.integral 𝓕 μ H D (Function.uncurry S.value) S.predictable B)))

include hI0 hI1 in
/-- The original physical equation implies the actual native split mild
identity under the SAME rotated noise. The split mild equation is proved,
not included as a premise. -/
theorem mild(q:ℝ≥0)(hq:q≤H):S.value q=ᵐ[μ]
    (fun ω=>NativeHeatObservation.heat (q:ℝ) u₀+
      I0.integral (additiveInput 𝓕 μ H D hH q) ω+
      I1.integral (residualInput 𝓕 μ H D B u₀ S hH q) ω):=by
  have hu:Measurable (S.value q):=
    (show IsStronglyPredictable 𝓕 S.value from S.predictable).stronglyAdapted q |>.measurable.mono (𝓕.le q) le_rfl
  have h0:Measurable (fun ω=>I0.integral (additiveInput 𝓕 μ H D hH q) ω):=(Lp.stronglyMeasurable _).measurable
  have h1:Measurable (fun ω=>I1.integral (residualInput 𝓕 μ H D B u₀ S hH q) ω):=(Lp.stronglyMeasurable _).measurable
  apply HeatObservationUniqueness.ae_eq μ _ _ hu ((measurable_const.add h0).add h1)
  intro ε hε x
  have hT:(q:ℝ)<(q:ℝ)+ε:=by linarith only [hε]
  have h0:=observe_terminal_integral I0 (leftIntegral 𝓕 μ H J) hI0 hκ (sq_nonneg _) f0
    stronglyMeasurable_const hT x (additiveInput 𝓕 μ H D hH q) (additive_kernel 𝓕 μ H D hH q hq)
  have h1:=observe_terminal_integral I1 (rightIntegral 𝓕 μ H J) hI1 D.ell_pos D.cap_nonneg f1 hf1
    hT x (residualInput 𝓕 μ H D B u₀ S hH q) (residual_kernel 𝓕 μ H D B u₀ S hH q hq)
  have he:=PredictableScalarHaarRotation.integral_originalRow 𝓕 μ H D U S.predictable B hT x
  have ha:=Lp.coeFn_add
    ((leftIntegral 𝓕 μ H J).integral (PredictableScalarHaarRotation.additiveRow 𝓕 μ H D hT x))
    ((rightIntegral 𝓕 μ H J).integral (PredictableScalarHaarRotation.residualRow 𝓕 μ H D U S.predictable hT x))
  rw [←he] at ha
  filter_upwards [S.equation q hq ε hε x,h0,h1,ha] with ω ho h0 h1 ha
  simp only [Pi.add_apply]
  rw [map_add,map_add]
  have hh:=NativeHeatObservation.functional_heat (τ:=ε) (t:=(q:ℝ)) hε q.2 x u₀
  rw [hh,show ε+(q:ℝ)=(q:ℝ)+ε by ring]
  have hgap:(q:ℝ)+ε-(q:ℝ)=ε:=by ring
  simp only [hgap] at h0 h1
  rw [ho,h0,h1]
  change functional ((q:ℝ)+ε) x u₀+B.integral _ ω=
    functional ((q:ℝ)+ε) x u₀+
      (leftIntegral 𝓕 μ H J).integral (PredictableScalarHaarRotation.additiveRow 𝓕 μ H D hT x) ω+
      (rightIntegral 𝓕 μ H J).integral (PredictableScalarHaarRotation.residualRow 𝓕 μ H D U S.predictable hT x) ω
  rw [ha]
  simp only [Pi.add_apply]
  ring

include hI0 hI1 in
/-- Preserve the given original state path while constructing the native
additive/residual model required by the checked comparison theorem. -/
def of_original:NativeMildFirst.Data 𝓕 μ H κ hκ D.residual_continuous.measurable
    D.ell_pos D.residual_bounds I0 I1 u₀ where
  value:=S.value
  continuous:=S.continuous
  predictable:=S.predictable
  coefficient:=hf1
  additiveInput:=additiveInput 𝓕 μ H D hH
  residualInput:=residualInput 𝓕 μ H D B u₀ S hH
  additive_kernel:=additive_kernel 𝓕 μ H D hH
  residual_kernel:=residual_kernel 𝓕 μ H D B u₀ S hH
  mild:=mild 𝓕 μ H D B u₀ S hH I0 I1 hI0 hI1

end SHE.OriginalNativeSplitMild
