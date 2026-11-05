module

public import SHEStochastic.CanonicalLinearFluctuation
public import SHEStochastic.WeakLimitMomentMartingale
public import SHEStochastic.WeakLimitSubGaussian

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHEStochastic.CanonicalLinearWeakLimit
open MeasureTheory ProbabilityTheory Filter SHE
open scoped NNReal ENNReal Topology
variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [Countable ι] [DecidableEq ι]
    (H : ℝ≥0) (L : E →L[ℝ] ℝ) (rate : ℝ)
local notation "X" => CanonicalContinuousStateDriver.Space (E := E) (ι := ι) H
local notation "M" => CanonicalLinearFluctuation.value (ι := ι) H L rate

/-- The scalar moment-based weak-limit argument applies unchanged to
any linear coordinate of a Hilbert-valued state. -/
theorem martingale (P : ℕ → ProbabilityMeasure X) (Q : ProbabilityMeasure X)
    (hlim : Tendsto P atTop (𝓝 Q)) (c : ℝ≥0 → ℝ≥0)
    (hSG : ∀ k t,HasSubgaussianMGF (M t) (c t) (P k : Measure X))
    (htest : ∀ k s t,s ≤ t → ∀ ψ : BoundedContinuousFunction X ℝ,
      (∫ x,ψ (CanonicalStateDriverFiltration.history H s x)*(M t x-M s x) ∂(P k : Measure X))=0) :
    Martingale M (CanonicalStateDriverFiltration.filtration H) (Q : Measure X) ∧
      ∀ t,HasSubgaussianMGF (M t) (c t) (Q : Measure X) := by
  letI : MetricSpace X := TopologicalSpace.metrizableSpaceMetric X
  have hm (k : ℕ) (t : ℝ≥0) := WeakLimitSubGaussian.square_bound (P k).toMeasure (hSG k t)
  refine ⟨?_,fun t => WeakLimitSubGaussian.limit P Q hlim (M t)
    (CanonicalLinearFluctuation.continuous H L rate t) (c t) (fun k => hSG k t)⟩
  exact WeakLimitMomentMartingale.martingale P Q hlim
    (CanonicalStateDriverFiltration.filtration H) (CanonicalStateDriverFiltration.history H)
    (WeakLimitCanonicalBrownian.continuous_history H) (fun _ => le_rfl) M
    (CanonicalLinearFluctuation.continuous H L rate) (CanonicalLinearFluctuation.adapted H L rate)
    (fun t => 1+48*Real.exp (1/2 : ℝ)*(c t : ℝ)^2)
    (fun k t => (hm k t).1) (fun k t => (hm k t).2) htest

end SHEStochastic.CanonicalLinearWeakLimit
