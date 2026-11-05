module
public import SHE.CanonicalStateDriverPredictable
public import SHE.OriginalNativeHeatParameterContinuity
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
namespace SHE.CanonicalHeatResidual
open MeasureTheory Set FiniteHaar DyadicApproximation AddCircle NativeHeatObservation
open scoped NNReal ENNReal Topology
local instance residual_unit : Fact (0<(1:ℝ)) := ⟨zero_lt_one⟩
local instance residual_circleSecond : SecondCountableTopology CircleHeat.CircleL2 :=
  (_root_.fourierBasis (T:=(1:ℝ))).repr.toHomeomorph.secondCountableTopology
local instance residual_realSecond : SecondCountableTopology RealL2 :=
  realCircleIdentification.toHomeomorph.secondCountableTopology
local instance residual_realSigma : MeasurableSpace RealL2 := borel _
local instance residual_realBorel : BorelSpace RealL2 := ⟨rfl⟩
variable (H : ℝ≥0)
local notation "R" => CanonicalContinuousStateDriver.Space (E:=RealL2) (ι:=HaarNode) H

def value (q : ℝ≥0) (ε : ℝ) (x : StoppedFourier.HeatCircle) (r : R) : ℝ :=
  functional ε x (CanonicalStateDriverFiltration.state H q r)-
    functional ((q:ℝ)+ε) x (CanonicalStateDriverFiltration.state H 0 r)

theorem measurable_value (q : ℝ≥0) (ε : ℝ) (x : StoppedFourier.HeatCircle) :
    Measurable (value H q ε x) := by
  apply Measurable.sub
  · exact (functional ε x).continuous.measurable.comp
      ((ContinuousMap.measurable_eval _).comp measurable_fst)
  · exact (functional ((q:ℝ)+ε) x).continuous.measurable.comp
      ((ContinuousMap.measurable_eval _).comp measurable_fst)

variable {Ω : Type*} [MeasurableSpace Ω]
variable (U : ℝ≥0→Ω→RealL2) (hc : ∀ω,Continuous (fun t=>U t ω))
variable (W : HaarNode→ℝ≥0→Ω→ℝ) (hd : ∀i ω,Continuous (fun t=>W i t ω))

theorem value_bundle (q : ℝ≥0) (hq : q≤H) (ε : ℝ) (x : StoppedFourier.HeatCircle) (ω : Ω) :
    value H q ε x (CanonicalContinuousStateDriver.bundle H U hc W hd ω)=
      functional ε x (U q ω)-functional ((q:ℝ)+ε) x (U 0 ω) := by
  unfold value
  rw [CanonicalStateDriverFiltration.state_eval H q hq,
    CanonicalStateDriverFiltration.state_eval H 0 (show (0:ℝ≥0)≤H from bot_le)]
  simp only [CanonicalContinuousStateDriver.state_eval,Real.toNNReal_coe]

/-- The canonical continuous state and coordinate processes reconstruct
the original state-and-driver point exactly. -/
theorem bundle_identity (r : R) :
    CanonicalContinuousStateDriver.bundle H (CanonicalStateDriverFiltration.state H)
      (CanonicalStateDriverFiltration.state_continuous H)
      (CanonicalStateDriverFiltration.coordinate H)
      (CanonicalStateDriverFiltration.coordinate_continuous H) r=r := by
  apply Prod.ext
  · apply ContinuousMap.ext
    intro t
    change r.1 (CanonicalStateDriverFiltration.clock H t.val.toNNReal)=r.1 t
    congr 1
    apply Subtype.ext
    simp only [CanonicalStateDriverFiltration.clock,Real.coe_toNNReal _ t.2.1,
      min_eq_left t.2.2]
  · funext i
    apply ContinuousMap.ext
    intro t
    change r.2 i (CanonicalStateDriverFiltration.clock H t.val.toNNReal)=r.2 i t
    congr 1
    apply Subtype.ext
    simp only [CanonicalStateDriverFiltration.clock,Real.coe_toNNReal _ t.2.1,
      min_eq_left t.2.2]
end SHE.CanonicalHeatResidual
