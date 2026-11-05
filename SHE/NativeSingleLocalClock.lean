module
public import SHE.GivenSingleNativeLocalUniqueness
public import SHE.NativeInverseClock
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false
namespace SHE.NativeSingleLocalClock
open MeasureTheory PredictableL2 NativeObservationNaturality DyadicApproximation
open scoped NNReal ENNReal
local instance localClock_unit : Fact (0<(1:ℝ)):=⟨zero_lt_one⟩
local instance localClock_realSecond : SecondCountableTopology RealL2:=
  FiniteHaar.realCircleIdentification.toHomeomorph.secondCountableTopology
local instance localClock_realSigma : MeasurableSpace RealL2:=borel _
local instance localClock_realBorel : BorelSpace RealL2:=⟨rfl⟩
variable{Ω:Type*}[MeasurableSpace Ω]
variable(μ:Measure Ω)[IsProbabilityMeasure μ]

def model_cast {F G:Filtration ℝ≥0 ‹MeasurableSpace Ω›}{T S:ℝ≥0}
    (hF:F=G)(hT:T=S)(D:SmoothApproximation.ScalarData)
    (I:StandardTerminalIto (C:=RealL2) (E:=ℝ) F μ T)
    (J:StandardTerminalIto (C:=RealL2) (E:=ℝ) G μ S)(hJ:HEq I J)(u₀:RealL2)
    (U:SingleNativeHeatEquation.Data F μ T D I u₀):
    SingleNativeHeatEquation.Data G μ S D J u₀:=by
  subst G
  subst S
  cases eq_of_heq hJ
  exact U

theorem model_cast_value {F G:Filtration ℝ≥0 ‹MeasurableSpace Ω›}{T S:ℝ≥0}
    (hF:F=G)(hT:T=S)(D:SmoothApproximation.ScalarData)
    (I:StandardTerminalIto (C:=RealL2) (E:=ℝ) F μ T)
    (J:StandardTerminalIto (C:=RealL2) (E:=ℝ) G μ S)(hJ:HEq I J)(u₀:RealL2)
    (U:SingleNativeHeatEquation.Data F μ T D I u₀):
    (model_cast μ hF hT D I J hJ u₀ U).value=U.value:=by
  subst G
  subst S
  cases eq_of_heq hJ
  rfl

theorem model_cast_law {F G:Filtration ℝ≥0 ‹MeasurableSpace Ω›}{T S:ℝ≥0}
    (hF:F=G)(hT:T=S)(D:SmoothApproximation.ScalarData)
    (I:StandardTerminalIto (C:=RealL2) (E:=ℝ) F μ T)
    (J:StandardTerminalIto (C:=RealL2) (E:=ℝ) G μ S)(hJ:HEq I J)(u₀:RealL2)
    (U:SingleNativeHeatEquation.Data F μ T D I u₀):
    HEq (NativePathLawComparison.law S μ (model_cast μ hF hT D I J hJ u₀ U).value
      (model_cast μ hF hT D I J hJ u₀ U).continuous)
      (NativePathLawComparison.law T μ U.value U.continuous):=by
  subst G
  subst S
  cases eq_of_heq hJ
  rfl

variable(F:Filtration ℝ≥0 ‹MeasurableSpace Ω›)(H:ℝ≥0)(D:SmoothApproximation.ScalarData)
variable(J:StandardTerminalIto (C:=RealL2) (E:=ℝ) F μ H)(u₀:RealL2)
variable(U:SingleNativeHeatEquation.Data F μ H D J u₀)

/-- Only the type's exact native clock round trip is changed. The given
state, actual scalar integral and physical equation are preserved. -/
def model:SingleNativeHeatEquation.Data
    (PredictableTimeDilation.filtration (NativeInverseClock.base F)
      (PredictableTimeDilation.clock NativeClock.rate NativeClock.rate_pos)) μ
    (NativeClock.rate*NativeClock.time H) D (NativeInverseClock.native F μ H J) u₀:=
  model_cast μ (NativeInverseClock.filtration_eq F).symm (NativeInverseClock.span_eq H).symm
    D J (NativeInverseClock.native F μ H J) (NativeInverseClock.native_heq F μ H J).symm u₀ U

theorem model_value:(model μ F H D J u₀ U).value=U.value:=
  model_cast_value μ (NativeInverseClock.filtration_eq F).symm (NativeInverseClock.span_eq H).symm
    D J (NativeInverseClock.native F μ H J) (NativeInverseClock.native_heq F μ H J).symm u₀ U

theorem model_law:
    HEq (NativePathLawComparison.law (NativeClock.rate*NativeClock.time H) μ
      (model μ F H D J u₀ U).value (model μ F H D J u₀ U).continuous)
      (NativePathLawComparison.law H μ U.value U.continuous):=
  model_cast_law μ (NativeInverseClock.filtration_eq F).symm (NativeInverseClock.span_eq H).symm
    D J (NativeInverseClock.native F μ H J) (NativeInverseClock.native_heq F μ H J).symm u₀ U

/-- The old local theorem's physical and native small-horizon bounds
follow from the prescribed native horizon bound. -/
theorem bounds(hH:0<H)(hH1:(H:ℝ)≤1):
    0<NativeClock.time H ∧ (NativeClock.time H:ℝ)≤1 ∧
      NativeClock.rate*NativeClock.time H≤1:=by
  refine ⟨NativeInverseClock.time_pos H hH,NativeInverseClock.time_le_one H hH1,?_⟩
  rw[NativeInverseClock.span_eq]
  exact_mod_cast hH1
end SHE.NativeSingleLocalClock
