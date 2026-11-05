module
public import SHE.OriginalNativeDenseObservationCompletion
public import SHE.CountableHeatObservations
public import SHE.RationalIntervalSequence
public import Mathlib.Topology.Sequences
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
set_option linter.unusedSectionVars false
namespace SHE.OriginalNativeCountableEquationCompletion
open MeasureTheory Set PredictableL2 StoppedFourier NativeHeatObservation DyadicApproximation FiniteHaar Filter
open scoped NNReal ENNReal Topology
local instance countableEquation_unit : Fact (0<(1:ℝ)):=⟨zero_lt_one⟩
local instance countableEquation_realSigma : MeasurableSpace RealL2:=borel _
local instance countableEquation_realBorel : BorelSpace RealL2:=⟨rfl⟩

/-- One fixed countable observation family for the entire local horizon. -/
abbrev Tests(H:ℝ≥0):=CanonicalConditionalRationalDriver.Times H × {a:ℚ // 0<a} × ℕ

def time{H:ℝ≥0}(a:Tests H):ℝ≥0:=(a.1.val:ℝ).toNNReal
def gap{H:ℝ≥0}(a:Tests H):ℝ:=a.2.1.val
def site{H:ℝ≥0}(a:Tests H):HeatCircle:=CountableHeatObservations.center a.2.2

theorem gap_pos{H:ℝ≥0}(a:Tests H):0<gap a:=by
  unfold gap
  exact_mod_cast a.2.1.property

theorem time_le{H:ℝ≥0}(a:Tests H):time a≤H:=by
  apply Real.toNNReal_le_iff_le_coe.mpr
  exact a.1.property.2

/-- Approximation stays in the SAME bounded time interval and in strictly
positive heat gaps. Irrational endpoints and the zero horizon are included. -/
theorem exists_sequence(H q:ℝ≥0)(hq:q≤H)(ε:ℝ)(hε:0<ε)(x:HeatCircle):
    ∃a:ℕ→Tests H,Tendsto (fun n=>time (a n)) atTop (𝓝 q) ∧
      Tendsto (fun n=>gap (a n)) atTop (𝓝 ε) ∧
      Tendsto (fun n=>site (a n)) atTop (𝓝 x):=by
  let qt:Icc (0:ℝ) (H:ℝ):=⟨q,q.2,by exact_mod_cast hq⟩
  obtain ⟨qs,hqs⟩:=RationalIntervalSequence.exists_sequence H qt
  have hqr:Tendsto (fun n=>(qs n).val:ℕ→ℝ) atTop (𝓝 (q:ℝ)):=by
    simpa only[Function.comp_def,CanonicalConditionalRationalDriver.time,qt] using
      (continuous_subtype_val.tendsto qt).comp hqs
  have hqt:Tendsto (fun n=>((qs n).val:ℝ).toNNReal) atTop (𝓝 q):=by
    simpa only[Function.comp_def,Real.toNNReal_coe] using
      continuous_real_toNNReal.tendsto (q:ℝ) |>.comp hqr
  obtain ⟨es,hesMono,hesI,hes⟩:=Rat.denseRange_cast.exists_seq_strictMono_tendsto_of_lt
    Rat.cast_strictMono.monotone hε
  obtain ⟨xs,hxs,hxt⟩:=mem_closure_iff_seq_limit.mp (CountableHeatObservations.center_dense x)
  choose js hjs using hxs
  have hxc:Tendsto (fun n=>CountableHeatObservations.center (js n)) atTop (𝓝 x):=by
    simpa only[hjs] using hxt
  let a:ℕ→Tests H:=fun n=>(qs n,⟨es n,by exact_mod_cast (hesI n).1⟩,js n)
  refine ⟨a,hqt,?_,hxc⟩
  simpa only[Function.comp_def,gap,a] using hes

variable{Ω:Type*}[MeasurableSpace Ω]
variable(D:SmoothApproximation.ScalarData)(U:ℝ≥0→Ω→RealL2)
variable(𝓕:Filtration ℝ≥0 ‹MeasurableSpace Ω›)(hU:IsStronglyPredictable 𝓕 U)
variable(μ:Measure Ω)[IsFiniteMeasure μ](H:ℝ≥0)

/-- All scalar positive-heat equations follow from this one countable
family. The SAME actual integral and actual row processes are preserved;
no conditional stochastic equation is postulated. -/
theorem equation_of_countable (J:StandardTerminalIto (C:=RealHaarInput) (E:=ℝ) 𝓕 μ H)
    (hc:∀ω,Continuous (fun t=>U t ω))
    (hcell:∀a:Tests H,OriginalNativeDenseObservationCompletion.residual U (time a) (gap a) (site a)=ᵐ[μ]
      (fun ω=>J.integral (OriginalNativeWhiteHeatRows.input D U 𝓕 hU μ H
        (time a) (gap a) (gap_pos a) (site a)) ω))
    (q:ℝ≥0)(hq:q≤H)(ε:ℝ)(hε:0<ε)(x:HeatCircle):
    OriginalNativeDenseObservationCompletion.residual U q ε x=ᵐ[μ]
      (fun ω=>J.integral (OriginalNativeWhiteHeatRows.input D U 𝓕 hU μ H q ε hε x) ω):=by
  obtain ⟨a,hq',he',hx'⟩:=exists_sequence H q hq ε hε x
  exact OriginalNativeDenseObservationCompletion.equation_of_sequence U D 𝓕 μ H hU J hc
    q ε hε x (fun n=>time (a n)) (fun n=>gap (a n)) (fun n=>gap_pos (a n))
    (fun n=>site (a n)) hq' he' hx' (fun n=>hcell (a n))
end SHE.OriginalNativeCountableEquationCompletion
