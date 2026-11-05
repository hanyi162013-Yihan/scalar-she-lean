module

public import SHEStochastic.UnboundedCoefficientCutoff
public import Mathlib.Analysis.Normed.Group.Bounded
public import Mathlib.Topology.UniformSpace.UniformConvergence

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace SHEStochastic.UnboundedCutoffConvergence
open Filter Set
open scoped NNReal Topology
variable {E V : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup V]

/-- On every bounded state set, all sufficiently large radial cutoffs
agree exactly with the original coefficient, for scalar or matrix output. -/
theorem eventually_eqOn (G : E → V) {s : Set E} (hs : Bornology.IsBounded s) :
    ∀ᶠ m : ℕ in atTop,EqOn (UnboundedCoefficientCutoff.coefficient G (m : ℝ≥0)) G s := by
  obtain ⟨R,hR⟩ := hs.exists_norm_le
  obtain ⟨N,hN⟩ := exists_nat_gt R
  refine eventually_atTop.mpr ⟨N,fun m hm x hx => ?_⟩
  exact UnboundedCoefficientCutoff.agrees G (m : ℝ≥0)
    ((hR x hx).trans (hN.le.trans (by exact_mod_cast hm)))

/-- The exact bounded-set agreement gives uniform convergence without
any differentiability or global boundedness of the original coefficient. -/
theorem uniformly_on_bounded (G : E → V) {s : Set E} (hs : Bornology.IsBounded s) :
    TendstoUniformlyOn (fun m : ℕ => UnboundedCoefficientCutoff.coefficient G (m : ℝ≥0)) G atTop s := by
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  filter_upwards [eventually_eqOn G hs] with m hm x hx
  rw [hm hx,dist_self]
  exact hε

theorem uniformly_on_compact (G : E → V) {s : Set E} (hs : IsCompact s) :
    TendstoUniformlyOn (fun m : ℕ => UnboundedCoefficientCutoff.coefficient G (m : ℝ≥0)) G atTop s :=
  uniformly_on_bounded G hs.isBounded

end SHEStochastic.UnboundedCutoffConvergence
