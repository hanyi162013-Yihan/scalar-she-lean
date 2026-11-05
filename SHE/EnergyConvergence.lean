module

public import SHE.KernelEnergyCauchy

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace SHE.KernelEnergyCauchy
open Filter
open scoped ENNReal Topology

theorem tendsto_of_energy_error {V : Type*} [NormedAddCommGroup V]
    (Y : ℕ → V) (Z : V) (e : ℕ → ℝ≥0∞) (he : Tendsto e atTop (𝓝 0))
    (hb : ∀ n, ENNReal.ofReal (‖Y n-Z‖^2) ≤ e n) : Tendsto Y atTop (𝓝 Z) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  have hev := he.eventually (gt_mem_nhds (ENNReal.ofReal_pos.mpr (sq_pos_of_pos hε)))
  obtain ⟨N,hN⟩ := eventually_atTop.mp hev
  refine ⟨N,?_⟩
  intro n hn
  have hs := (hb n).trans_lt (hN n hn)
  have hr : ‖Y n-Z‖^2 < ε^2 := (ENNReal.ofReal_lt_ofReal_iff (by positivity)).mp hs
  rw [dist_eq_norm]
  nlinarith [norm_nonneg (Y n-Z)]

end SHE.KernelEnergyCauchy
