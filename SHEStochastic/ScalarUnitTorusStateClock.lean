module

public import SHE.NativeContinuousPath
public import SHE.HaarRealSpace
public import SHE.TimeDilationPathPull
public import SHE.NativeClock

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section

namespace SHEStochastic.ScalarUnitTorusStateClock
open MeasureTheory Set SHE SHE.PredictableL2 SHE.PredictableTimeDilation SHE.DyadicApproximation SHE.StoppedFourier SHE.FiniteHaar
open scoped NNReal ENNReal

local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance : SecondCountableTopology CircleHeat.CircleL2 :=
  (_root_.fourierBasis (T := (1 : ℝ))).repr.toHomeomorph.secondCountableTopology
local instance : SecondCountableTopology RealL2 := realCircleIdentification.toHomeomorph.secondCountableTopology
local instance : MeasurableSpace RealL2 := borel _
local instance : BorelSpace RealL2 := ⟨rfl⟩
local notation "r" => NativeClock.rate
local notation "hr" => NativeClock.rate_pos

variable {Ω : Type*} [MeasurableSpace Ω] (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›)

/-- The state itself has no Brownian Jacobian. -/
def native (W : ℝ≥0 → Ω → RealL2) (s : ℝ≥0) : Ω → RealL2 :=
  W ((clock r hr).symm s)

theorem predictable (W : ℝ≥0 → Ω → RealL2)
    (hW : StronglyMeasurable[F.predictable] (Function.uncurry W)) :
    StronglyMeasurable[(filtration F (clock NativeClock.rate NativeClock.rate_pos)).predictable]
      (Function.uncurry (native W)) :=
  hW.comp_measurable (measurable_backward F (clock r hr))

omit [MeasurableSpace Ω] in
theorem continuous_native (W : ℝ≥0 → Ω → RealL2)
    (hc : ∀ ω, Continuous (fun t => W t ω)) (ω : Ω) :
    Continuous (fun s => native W s ω) := (hc ω).comp (clock_symm_continuous r hr)

omit [MeasurableSpace Ω] in
theorem pull_native (W : ℝ≥0 → Ω → RealL2) : pullPath r hr (native W)=W := by
  funext t ω
  simp only [pullPath,native,OrderIso.symm_apply_apply]

omit [MeasurableSpace Ω] in
theorem native_zero (W : ℝ≥0 → Ω → RealL2) : native W 0=W 0 := by
  change W (r⁻¹*0)=W 0
  rw [mul_zero]

/-- Pull a continuous path to the manuscript clock on its entire closed horizon. -/
def timeMap (H : ℝ≥0) : C(Icc (0 : ℝ) (H : ℝ), Icc (0 : ℝ) ((r*H : ℝ≥0) : ℝ)) :=
  ⟨fun t => ⟨(r : ℝ)*t.val, mul_nonneg (show (0 : ℝ)≤r from (hr).le) t.property.1,
    by
      rw [NNReal.coe_mul]
      exact mul_le_mul_of_nonneg_left t.property.2 (show (0 : ℝ)≤r from (hr).le)⟩,
    (continuous_const.mul continuous_subtype_val).subtype_mk _⟩

def pull (H : ℝ≥0) (Y : C(Icc (0 : ℝ) ((r*H : ℝ≥0) : ℝ), RealL2)) :
    C(Icc (0 : ℝ) (H : ℝ), RealL2) := Y.comp (timeMap H)

theorem measurable_pull (H : ℝ≥0) : Measurable (pull H) :=
  ContinuousMap.measurable_iff_eval.mpr
    (fun t => ContinuousMap.measurable_eval (timeMap H t))

omit [MeasurableSpace Ω] in
theorem path_pull (H : ℝ≥0) (U : ℝ≥0 → Ω → RealL2)
    (hc : ∀ ω, Continuous (fun t => U t ω)) :
    pull H ∘ NativeContinuousPath.path (r*H) U hc =
      NativeContinuousPath.path H (pullPath r hr U) (pullPath_continuous r hr U hc) := by
  funext ω
  apply ContinuousMap.ext
  intro t
  change U ((r : ℝ)*t.val).toNNReal ω = U (r*t.val.toNNReal) ω
  rw [Real.toNNReal_mul (show (0 : ℝ)≤r from (hr).le),Real.toNNReal_coe]

end SHEStochastic.ScalarUnitTorusStateClock
