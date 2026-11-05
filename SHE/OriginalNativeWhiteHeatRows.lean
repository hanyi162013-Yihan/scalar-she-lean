module
public import SHE.OriginalNativeHeatParameterContinuity
public import SHE.OriginalNativeFrozenRows
public import SHE.StoppedItoInputs
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
set_option linter.unusedSectionVars false
namespace SHE.OriginalNativeWhiteHeatRows
open MeasureTheory Set PredictableL2 StoppedFourier DyadicApproximation FiniteHaar
open scoped NNReal ENNReal
local instance whiteHeatRows_unit : Fact (0<(1:ℝ)):=⟨zero_lt_one⟩
local instance whiteHeatRows_circleSecond : SecondCountableTopology CircleHeat.CircleL2:=
  (_root_.fourierBasis (T:=(1:ℝ))).repr.toHomeomorph.secondCountableTopology
local instance whiteHeatRows_realSecond : SecondCountableTopology RealL2:=
  realCircleIdentification.toHomeomorph.secondCountableTopology
local instance whiteHeatRows_realSigma : MeasurableSpace RealL2:=borel _
local instance whiteHeatRows_realBorel : BorelSpace RealL2:=⟨rfl⟩
local instance whiteHeatRows_rowSigma : MeasurableSpace RealHaarInput:=borel _
local instance whiteHeatRows_rowBorel : BorelSpace RealHaarInput:=⟨rfl⟩
variable{Ω:Type*}[MeasurableSpace Ω]
variable(D:SmoothApproximation.ScalarData)(U:ℝ≥0→Ω→RealL2)

def raw(q:ℝ≥0)(ε:ℝ)(x:HeatCircle)(p:ℝ≥0×Ω):RealHaarInput:=
  if p.1<q then OriginalNativeFrozenRows.coordinates.symm
    (OriginalNativeRowContinuity.row D ((q:ℝ)+ε) x p.1 (U p.1 p.2)) else 0

theorem raw_eq_target(q:ℝ≥0)(ε:ℝ)(x:HeatCircle):
    raw D U q ε x=BoundedContinuousRowFreezing.target q
      (OriginalNativeFrozenRows.row D q ((q:ℝ)+ε) x) U:=by
  funext p
  unfold raw BoundedContinuousRowFreezing.target OriginalNativeFrozenRows.row
  split_ifs with hp
  · simp only[min_eq_left hp.le]
  · rfl

theorem raw_norm_le(q:ℝ≥0)(ε:ℝ)(hε:0<ε)(x:HeatCircle)(p:ℝ≥0×Ω):
    ‖raw D U q ε x p‖≤OriginalNativeFrozenRows.bound D q ((q:ℝ)+ε):=by
  rw[raw_eq_target]
  unfold BoundedContinuousRowFreezing.target
  split_ifs with hp
  · exact OriginalNativeFrozenRows.row_norm_le D q ((q:ℝ)+ε) x (by linarith) _
  · rw[norm_zero]
    exact Real.sqrt_nonneg _

variable(𝓕:Filtration ℝ≥0 ‹MeasurableSpace Ω›)
variable(hU:IsStronglyPredictable 𝓕 U)
include hU in
/-- The bounded before-q original row is genuinely predictable in the
SAME fixed physical Haar coordinates. -/
theorem raw_predictable(q:ℝ≥0)(ε:ℝ)(hε:0<ε)(x:HeatCircle):
    StronglyMeasurable[𝓕.predictable] (raw D U q ε x):=by
  have ht:@Measurable (ℝ≥0×Ω) (Iic q) 𝓕.predictable _
      (fun p=>⟨min p.1 q,min_le_right _ _⟩):=
    ((PredictableClock.time_measurable 𝓕).min measurable_const).subtype_mk
  have hm:= (OriginalNativeFrozenRows.row_continuous D q ((q:ℝ)+ε) x (by linarith)).comp_stronglyMeasurable
    (ht.stronglyMeasurable.prodMk hU)
  have he:raw D U q ε x=(fun p:ℝ≥0×Ω=>if p.1<q then
      OriginalNativeFrozenRows.row D q ((q:ℝ)+ε) x
        (⟨min p.1 q,min_le_right _ _⟩,U p.1 p.2) else 0):=by
    funext p
    by_cases hp:p.1<q
    · simp only[raw,ite_eq_left hp,OriginalNativeFrozenRows.row,min_eq_left hp.le]
    · simp only[raw,ite_eq_right hp]
  rw[he]
  exact hm.ite (measurableSet_lt (PredictableClock.time_measurable 𝓕) measurable_const)
    stronglyMeasurable_const

variable(μ:Measure Ω)[IsFiniteMeasure μ](H:ℝ≥0)
include hU in
theorem raw_memLp(q:ℝ≥0)(ε:ℝ)(hε:0<ε)(x:HeatCircle):
    @MemLp (ℝ≥0×Ω) RealHaarInput 𝓕.predictable _ _ (raw D U q ε x) 2
      ((energyMeasure μ H).trim (predictable_le_product 𝓕)):=by
  haveI:IsFiniteMeasure (energyMeasure μ H):=by unfold energyMeasure;infer_instance
  exact MemLp.of_bound (raw_predictable D U 𝓕 hU q ε hε x).aestronglyMeasurable
    (OriginalNativeFrozenRows.bound D q ((q:ℝ)+ε)) (ae_of_all _ (raw_norm_le D U q ε hε x))

def input(q:ℝ≥0)(ε:ℝ)(hε:0<ε)(x:HeatCircle):Process (E:=RealHaarInput) 𝓕 μ H:=
  (raw_memLp D U 𝓕 hU μ H q ε hε x).toLp (raw D U q ε x)

theorem input_ae(q:ℝ≥0)(ε:ℝ)(hε:0<ε)(x:HeatCircle):
    input D U 𝓕 hU μ H q ε hε x=ᵐ[energyMeasure μ H] raw D U q ε x:=
  ae_eq_of_ae_eq_trim (raw_memLp D U 𝓕 hU μ H q ε hε x).coeFn_toLp
end SHE.OriginalNativeWhiteHeatRows
