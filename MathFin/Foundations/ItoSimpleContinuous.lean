/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import MathFin.Foundations.ItoIntegralProcessMartingale

/-! Pure sample-path continuity excerpt; local-martingale packaging is kept in
ItoIntegralProcessLocalMartingale and is not needed for continuous versions. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace MathFin
namespace ItoIntegralProcess

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
  {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B μ)

include hB

omit hB in
/-- **Pathwise continuity of the elementary Itô integral.** Given continuous
Brownian paths, for each `ω` the path `t ↦ (V ● B)_t ω` is continuous: it is the
finite sum `∑_p V(p)ω·(B_{p.2∧t}ω − B_{p.1∧t}ω)` (`itoSimpleProcess_apply`), each
summand the continuous path `B(·)ω` composed with the continuous clamp
`t ↦ min p.i t`. -/
theorem itoSimpleProcess_pathContinuous (hBmeas : ∀ t, Measurable (B t))
    (hBcont : ∀ ω, Continuous fun t : ℝ≥0 ↦ B t ω)
    (V : SimpleProcess ℝ (ItoIntegralL2.natFiltration (mΩ := mΩ) hBmeas)) (ω : Ω) :
    Continuous fun t : ℝ≥0 ↦ itoSimpleProcess hBmeas V t ω := by
  simp_rw [fun t ↦ itoSimpleProcess_apply hBmeas V t ω, Finsupp.sum]
  refine continuous_finsetSum _ fun p _ ↦ ?_
  refine continuous_const.mul (Continuous.sub ?_ ?_)
  · exact (hBcont ω).comp (continuous_const.min continuous_id)
  · exact (hBcont ω).comp (continuous_const.min continuous_id)

end ItoIntegralProcess
end MathFin
