module

public import Mathlib.Analysis.Normed.Operator.Banach
public import Mathlib.Topology.UniformSpace.UniformApproximation
public import Mathlib.Tactic

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace SHE.StrongOperator
open scoped NNReal

variable {𝕜 X E F : Type*} [NontriviallyNormedField 𝕜] [TopologicalSpace X]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- Uniformly bounded operator actions preserve continuity when the input
is obtained as an actual norm limit of continuous test-vector actions. -/
theorem continuous_action_of_approximation {ι : Type*} {l : Filter ι} [l.NeBot]
    (A : X → E →L[𝕜] F) (K : ℝ) (_hK : 0 ≤ K)
    (hA : ∀ p x, ‖A p x‖ ≤ K * ‖x‖) (v : E) (u : ι → E)
    (hu : Filter.Tendsto u l (nhds v))
    (hc : ∀ n, Continuous (fun p => A p (u n))) : Continuous (fun p => A p v) := by
  have hz : Filter.Tendsto (fun n => (K + 1) * ‖v - u n‖) l (nhds 0) := by
    have h0 : Filter.Tendsto (fun n => v - u n) l (nhds (v - v)) :=
      tendsto_const_nhds.sub hu
    have hh := h0.norm.const_mul (K + 1)
    simpa only [sub_self, norm_zero, mul_zero] using hh
  have hunif : TendstoUniformly (fun n p => A p (u n)) (fun p => A p v) l := by
    apply Metric.tendstoUniformly_iff.mpr
    intro ε hε
    filter_upwards [hz.eventually (gt_mem_nhds hε)] with n hn p
    rw [dist_eq_norm, ← map_sub]
    exact (hA p (v - u n)).trans_lt ((mul_le_mul_of_nonneg_right (by linarith : K ≤ K + 1)
      (norm_nonneg _)).trans_lt hn)
  exact hunif.continuous (Filter.Eventually.frequently (Filter.Eventually.of_forall hc))

theorem continuous_joint_action (A : X → E →L[𝕜] F) (K : ℝ) (hK : 0 ≤ K)
    (hA : ∀ p x, ‖A p x‖ ≤ K * ‖x‖) (hc : ∀ x, Continuous (fun p => A p x)) :
    Continuous (fun p : X × E => A p.1 p.2) := by
  let K' : ℝ≥0 := ⟨K, hK⟩
  apply continuous_prod_of_continuous_lipschitzWith' _ K'
  · intro p
    apply LipschitzWith.of_dist_le_mul
    intro x y
    rw [dist_eq_norm, ← map_sub, dist_eq_norm]
    exact hA p (x - y)
  · exact hc

/-- Strong continuity of inverses follows from strong continuity and a
uniform inverse bound; no operator-norm continuity is assumed. -/
theorem continuous_inverse_action (A : X → E ≃L[𝕜] F) (K : ℝ)
    (hA : ∀ p y, ‖(A p).symm y‖ ≤ K * ‖y‖)
    (hc : ∀ x, Continuous (fun p => A p x)) (v : F) :
    Continuous (fun p => (A p).symm v) := by
  apply continuous_iff_continuousAt.mpr
  intro p
  change Filter.Tendsto (fun q => (A q).symm v) (nhds p) (nhds ((A p).symm v))
  rw [tendsto_iff_norm_sub_tendsto_zero]
  let x := (A p).symm v
  have hres : Filter.Tendsto (fun q => v - A q x) (nhds p) (nhds 0) := by
    have hh : Filter.Tendsto (fun q => v - A q x) (nhds p) (nhds (v - A p x)) :=
      tendsto_const_nhds.sub ((hc x).tendsto p)
    simpa only [x, ContinuousLinearEquiv.apply_symm_apply, sub_self] using hh
  have hbound (q : X) : ‖(A q).symm v - (A p).symm v‖ ≤ K * ‖v - A q x‖ := by
    have he : (A q).symm v - (A p).symm v = (A q).symm (v - A q x) := by
      rw [map_sub, ContinuousLinearEquiv.symm_apply_apply]
    rw [he]
    exact hA q _
  exact squeeze_zero (fun _ => norm_nonneg _) hbound (by simpa using hres.norm.const_mul K)

end SHE.StrongOperator
