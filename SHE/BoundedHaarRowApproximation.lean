module
public import SHE.BoundedRowStepConvergence
public import SHE.FiniteHaarProjectionL2
public import SHE.StandardTerminalIto
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false
namespace SHE.BoundedHaarRowApproximation
open MeasureTheory Set PredictableL2 FiniteHaar Filter
open scoped NNReal ENNReal Topology
local instance boundedHaar_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance boundedHaar_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
variable {Ω E : Type*} [MeasurableSpace Ω]
variable [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ]
variable (H q : ℝ≥0) (R : Iic q×E→RealHaarInput) (hR : Continuous R)
variable (U : ℝ≥0→Ω→E) (hUa : StronglyAdapted 𝓕 U)
variable (M : ℝ) (hb : ∀p,‖R p‖≤M)

/-- The actual finite time and finite Haar approximation, in the genuine
predictable L2 space of the supplied probability space. -/
def input (n : ℕ) : Process (E:=RealHaarInput) 𝓕 μ H := by
  letI : MeasurableSpace (ℝ≥0×Ω) := 𝓕.predictable
  exact FiniteHaarProjectionL2.projection ((energyMeasure μ H).trim (predictable_le_product 𝓕))
    (nodesBelow n) (BoundedRowStepInputs.input 𝓕 μ H q R hR U hUa M hb n)

theorem input_ae (n : ℕ) : input 𝓕 μ H q R hR U hUa M hb n=ᵐ[energyMeasure μ H]
    (fun p=>FiniteHaarColumnProjection.projection (nodesBelow n)
      (BoundedContinuousRowFreezing.value q R U n p)) := by
  have hp : input 𝓕 μ H q R hR U hUa M hb n=ᵐ[energyMeasure μ H]
      (fun p=>FiniteHaarColumnProjection.projection (nodesBelow n)
        (BoundedRowStepInputs.input 𝓕 μ H q R hR U hUa M hb n p)) := by
    apply ae_eq_of_ae_eq_trim
    letI : MeasurableSpace (ℝ≥0×Ω) := 𝓕.predictable
    exact FiniteHaarProjectionL2.projection_ae
      ((energyMeasure μ H).trim (predictable_le_product 𝓕)) (nodesBelow n)
      (BoundedRowStepInputs.input 𝓕 μ H q R hR U hUa M hb n)
  filter_upwards [hp,BoundedRowStepInputs.input_frozen_ae 𝓕 μ H q R hR U hUa M hb n] with p hp hf
  change input 𝓕 μ H q R hR U hUa M hb n p=_
  exact hp.trans (congrArg (FiniteHaarColumnProjection.projection (nodesBelow n)) hf)

theorem input_tendsto (hU : Measurable (Function.uncurry U))
    (hc : ∀ω,Continuous (fun s=>U s ω)) (hM : 0≤M)
    (f : Process (E:=RealHaarInput) 𝓕 μ H)
    (hf : f=ᵐ[energyMeasure μ H] BoundedContinuousRowFreezing.target q R U) :
    Tendsto (input 𝓕 μ H q R hR U hUa M hb) atTop (𝓝 f) := by
  letI : MeasurableSpace (ℝ≥0×Ω) := 𝓕.predictable
  exact FiniteHaarProjectionL2.diagonal _
    (BoundedRowStepInputs.input_tendsto 𝓕 μ H q R hR U hUa M hb hU hc hM f hf)

theorem integral_tendsto (J : StandardTerminalIto (C:=RealHaarInput) (E:=ℝ) 𝓕 μ H)
    (hU : Measurable (Function.uncurry U)) (hc : ∀ω,Continuous (fun s=>U s ω)) (hM : 0≤M)
    (f : Process (E:=RealHaarInput) 𝓕 μ H)
    (hf : f=ᵐ[energyMeasure μ H] BoundedContinuousRowFreezing.target q R U) :
    Tendsto (fun n=>J.integral (input 𝓕 μ H q R hR U hUa M hb n)) atTop (𝓝 (J.integral f)) :=
  (J.integral.continuous.tendsto f).comp (input_tendsto 𝓕 μ H q R hR U hUa M hb hU hc hM f hf)

/-- An original-sample subsequence is derived from the same integral's
L2 convergence; no stochastic approximation statement is assumed. -/
theorem exists_ae_subsequence (J : StandardTerminalIto (C:=RealHaarInput) (E:=ℝ) 𝓕 μ H)
    (hU : Measurable (Function.uncurry U)) (hc : ∀ω,Continuous (fun s=>U s ω)) (hM : 0≤M)
    (f : Process (E:=RealHaarInput) 𝓕 μ H)
    (hf : f=ᵐ[energyMeasure μ H] BoundedContinuousRowFreezing.target q R U) :
    ∃ns:ℕ→ℕ,StrictMono ns ∧ ∀ᵐω∂μ,
      Tendsto (fun n=>(J.integral (input 𝓕 μ H q R hR U hUa M hb (ns n)):Lp ℝ 2 μ) ω)
        atTop (𝓝 ((J.integral f:Lp ℝ 2 μ) ω)) := by
  have ht := integral_tendsto 𝓕 μ H q R hR U hUa M hb J hU hc hM f hf
  exact (tendstoInMeasure_of_tendsto_Lp (p:=2) (μ:=μ) ht).exists_seq_tendsto_ae
end SHE.BoundedHaarRowApproximation
