module

public import Mathlib.Topology.MetricSpace.Cauchy
public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace SHE.KernelEnergyCauchy
open Filter
open scoped ENNReal Topology

/-- Integrated squared kernel errors control Cauchy convergence of the
actual stochastic outputs. This elementary closure does not assume a
parameterized stochastic integral or its measurable version. -/
theorem cauchy_of_energy_error {V : Type*} [NormedAddCommGroup V]
    (Y : ℕ → V) (e : ℕ → ℝ≥0∞) (he : Tendsto e atTop (𝓝 0))
    (hb : ∀ n m,ENNReal.ofReal (‖Y n-Y m‖^2) ≤ 2*e n+2*e m) : CauchySeq Y := by
  apply Metric.cauchySeq_iff.mpr
  intro ε hε
  have hδ : 0 < ε^2/8 := by positivity
  have hev := he.eventually (gt_mem_nhds (ENNReal.ofReal_pos.mpr hδ))
  obtain ⟨N,hN⟩ := eventually_atTop.mp hev
  refine ⟨N,?_⟩
  intro n hn m hm
  have hs : ENNReal.ofReal (‖Y n-Y m‖^2) ≤
      2*ENNReal.ofReal (ε^2/8)+2*ENNReal.ofReal (ε^2/8) :=
    (hb n m).trans (add_le_add (mul_le_mul_right (hN n hn).le 2) (mul_le_mul_right (hN m hm).le 2))
  have heq : (2:ℝ≥0∞)*ENNReal.ofReal (ε^2/8)+2*ENNReal.ofReal (ε^2/8)=
      ENNReal.ofReal (ε^2/2) := by
    rw [show (2:ℝ≥0∞)=ENNReal.ofReal 2 by norm_num,← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2),
      ← ENNReal.ofReal_add (by positivity) (by positivity)]
    congr 1
    ring
  rw [heq] at hs
  have hreal := (ENNReal.ofReal_le_ofReal_iff (by positivity : (0:ℝ) ≤ ε^2/2)).mp hs
  rw [dist_eq_norm]
  nlinarith [norm_nonneg (Y n-Y m)]

end SHE.KernelEnergyCauchy
