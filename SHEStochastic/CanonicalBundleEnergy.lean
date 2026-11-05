module

public import SHEStochastic.SeparateCanonicalCompactness
public import Mathlib.MeasureTheory.Integral.Lebesgue.Map

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 900000
noncomputable section

namespace SHEStochastic.CanonicalBundleEnergy
open MeasureTheory Filter SHE
open scoped NNReal ENNReal Topology
variable {Ω E ι : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    [Countable ι] [DecidableEq ι]
    (F : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω))
    (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
    (P : FiniteScalarIto.Family F μ H ι)
    (U : ℝ≥0 → Ω → E) (hc : ∀ ω,Continuous (fun t => U t ω))

/-- The joint canonical bundle retains the original whole state path. -/
theorem state (ω : Ω) : (CanonicalNativeBrownian.bundle F μ H P U hc ω).1=
    NativeContinuousPath.path H U hc ω := by
  apply ContinuousMap.ext
  intro t
  change U (0+t.val.toNNReal) ω=U t.val.toNNReal ω
  rw [zero_add]

/-- Exact transport of full state-path energy tails to the joint law.
The original driver coordinate and state/driver dependence are retained. -/
theorem tail (hU : ∀ t,Measurable[F t] (U t)) (R : ℝ) :
    (∫⁻ x in {x | R≤‖x.1‖^2},ENNReal.ofReal (‖x.1‖^2)
      ∂μ.map (CanonicalNativeBrownian.bundle F μ H P U hc))=
    ∫⁻ ω in {ω | R≤‖NativeContinuousPath.path H U hc ω‖^2},
      ENNReal.ofReal (‖NativeContinuousPath.path H U hc ω‖^2) ∂μ := by
  have hm := CanonicalNativeBrownian.measurable_bundle F μ H P U hc hU
  rw [setLIntegral_map (measurableSet_le measurable_const (by fun_prop)) (by fun_prop) hm]
  simp only [Set.preimage_setOf_eq,state F μ H P U hc]

end SHEStochastic.CanonicalBundleEnergy
