module
public import SHE.CanonicalBoundedHaarIdentification
public import SHE.OriginalSingleHaarApproximation
public import SHE.CanonicalHeatResidual
public import SHE.NativeSingleNoiseBasis
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1700000
set_option linter.unusedSectionVars false
namespace SHE.CanonicalOriginalHeatSums
open MeasureTheory Set FiniteHaar DyadicApproximation AddCircle PredictableL2 Filter
open scoped NNReal ENNReal Topology
local instance heatSums_unit : Fact (0<(1:ℝ)) := ⟨zero_lt_one⟩
local instance heatSums_circleSecond : SecondCountableTopology CircleHeat.CircleL2 :=
  (_root_.fourierBasis (T:=(1:ℝ))).repr.toHomeomorph.secondCountableTopology
local instance heatSums_realSecond : SecondCountableTopology RealL2 :=
  realCircleIdentification.toHomeomorph.secondCountableTopology
local instance heatSums_realSigma : MeasurableSpace RealL2 := borel _
local instance heatSums_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance heatSums_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance heatSums_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
variable (H : ℝ≥0) (D : SmoothApproximation.ScalarData)
variable (q : ℝ≥0) (hq : q≤H) (ε : ℝ) (x : StoppedFourier.HeatCircle)

/-- A literal measurable finite time/Haar sum, independent of which
probability measure will later be put on the canonical space. -/
def value (n : ℕ) : CanonicalContinuousStateDriver.Space (E:=RealL2) (ι:=HaarNode) H→ℝ :=
  CanonicalScalarItoSums.value H (CanonicalBoundedHaarIdentification.time q n)
    (fun k=>CanonicalBoundedHaarIdentification.time_le H q n k hq)
    (CanonicalBoundedHaarIdentification.row q (OriginalNativeFrozenRows.row D q ((q:ℝ)+ε) x) n)
    (CanonicalBoundedHaarIdentification.indices q n)

theorem measurable_value (hε : 0<ε) (n : ℕ) : Measurable (value H D q hq ε x n) :=
  CanonicalScalarItoSums.value_measurable _ _ _ _ _
    (CanonicalBoundedHaarIdentification.row_measurable q _
      (OriginalNativeFrozenRows.row_continuous D q ((q:ℝ)+ε) x (by linarith)) n)

variable {Ω : Type*} [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ]
variable (U : ℝ≥0→Ω→RealL2) (hc : ∀ω,Continuous (fun t=>U t ω)) (hU : IsStronglyPredictable 𝓕 U)
variable (J : StandardTerminalIto (C:=RealHaarInput) (E:=ℝ) 𝓕 μ H)
variable (W : HaarNode→ℝ≥0→Ω→ℝ) (hd : ∀i ω,Continuous (fun t=>W i t ω))

theorem integral_eq (hε : 0<ε) (hlocal : StandardTerminalPastLocality J)
    (hW : ∀i t,t≤H→W i t=ᵐ[μ] CanonicalScalarItoCells.coordinate H i 𝓕 μ J t) (n : ℕ) :
    J.integral (OriginalSingleHaarApproximation.approximation 𝓕 μ H D U hU q ε hε x n)=ᵐ[μ]
      (fun ω=>value H D q hq ε x n (CanonicalContinuousStateDriver.bundle H U hc W hd ω)) :=
  CanonicalBoundedHaarIdentification.integral_eq 𝓕 μ H q _
    (OriginalNativeFrozenRows.row_continuous D q ((q:ℝ)+ε) x (by linarith)) U hU.stronglyAdapted
    (OriginalNativeFrozenRows.bound D q ((q:ℝ)+ε))
    (OriginalNativeFrozenRows.row_norm_le D q ((q:ℝ)+ε) x (by linarith)) n hq (Real.sqrt_nonneg _)
    J hlocal hc W hd (fun i k=>hW i _ (CanonicalBoundedHaarIdentification.time_le H q n k hq))

/-- The actual weak observed equation identifies an original-sample
subsequence limit of the explicit canonical sums. -/
theorem exists_observed_limit (hε : 0<ε) (hlocal : StandardTerminalPastLocality J)
    (hW : ∀i t,t≤H→W i t=ᵐ[μ] CanonicalScalarItoCells.coordinate H i 𝓕 μ J t)
    (heq : (fun ω=>CanonicalHeatResidual.value H q ε x
      (CanonicalContinuousStateDriver.bundle H U hc W hd ω))=ᵐ[μ]
        J.integral (OriginalNativeWhiteHeatRows.input D U 𝓕 hU μ H q ε hε x)) :
    ∃ns:ℕ→ℕ,StrictMono ns ∧ ∀ᵐω∂μ,
      Tendsto (fun n=>value H D q hq ε x (ns n)
        (CanonicalContinuousStateDriver.bundle H U hc W hd ω)) atTop
        (𝓝 (CanonicalHeatResidual.value H q ε x
          (CanonicalContinuousStateDriver.bundle H U hc W hd ω))) := by
  have ht := (J.integral.continuous.tendsto
    (OriginalNativeWhiteHeatRows.input D U 𝓕 hU μ H q ε hε x)).comp
      (OriginalSingleHaarApproximation.approximation_tendsto 𝓕 μ H D U hU q ε hε x hc)
  obtain ⟨ns,hns,ha⟩ := (tendstoInMeasure_of_tendsto_Lp (p:=2) (μ:=μ) ht).exists_seq_tendsto_ae
  have hi := ae_all_iff.mpr (fun n=>integral_eq H D q hq ε x 𝓕 μ U hc hU J W hd hε hlocal hW (ns n))
  refine ⟨ns,hns,?_⟩
  filter_upwards [ha,heq,hi] with ω ha heq hi
  rw [heq]
  exact ha.congr' (Filter.Eventually.of_forall (fun n=>hi n))
end SHE.CanonicalOriginalHeatSums
