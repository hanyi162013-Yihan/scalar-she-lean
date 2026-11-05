module

public import SHE.GaussianAffineItoTest

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
noncomputable section

namespace SHE.ClippedExponential
open Set Filter
open scoped NNReal Topology

/-- The clipping only extends the physical nonnegative time formula
to a globally bounded deterministic test. -/
def damping (Λ t : ℝ) : ℝ := Real.exp (-Λ*max t 0)

theorem continuous_damping (Λ : ℝ) : Continuous (damping Λ) := by
  unfold damping
  fun_prop

theorem damping_eq {Λ t : ℝ} (ht : 0≤t) : damping Λ t=Real.exp (-Λ*t) := by
  simp only [damping,max_eq_left ht]

theorem damping_pos (Λ t : ℝ) : 0<damping Λ t := Real.exp_pos _

theorem damping_le_one {Λ : ℝ} (hΛ : 0≤Λ) (t : ℝ) : damping Λ t≤1 := by
  exact Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hΛ) (le_max_right _ _))

theorem hasDerivAt_damping {Λ t : ℝ} (ht : 0<t) :
    HasDerivAt (damping Λ) (-Λ*damping Λ t) t := by
  have hh := ((hasDerivAt_id t).const_mul (-Λ)).exp
  simp only [id_eq,mul_one] at hh
  have he : damping Λ=ᶠ[𝓝 t] (fun r => Real.exp (-Λ*r)) := by
    filter_upwards [eventually_gt_nhds ht] with r hr
    exact damping_eq hr.le
  have hr := hh.congr_of_eventuallyEq he
  simpa only [damping_eq ht.le,mul_comm] using hr

theorem lipschitz_damping {Λ : ℝ} (hΛ : 0≤Λ) :
    LipschitzWith ⟨Λ,hΛ⟩ (damping Λ) := by
  have hExp : LipschitzOnWith ⟨Λ,hΛ⟩ (fun t : ℝ => Real.exp (-Λ*t)) (Ici 0) := by
    apply (convex_Ici (0:ℝ)).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
      (fun t _ => (((hasDerivAt_id t).const_mul (-Λ)).exp).hasDerivWithinAt)
    intro t ht
    apply NNReal.coe_le_coe.mp
    simp only [id_eq,mul_one,coe_nnnorm]
    rw [norm_mul,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _),norm_neg,Real.norm_eq_abs,abs_of_nonneg hΛ]
    have hh : Real.exp (-Λ*t)≤1 := Real.exp_le_one_iff.mpr
      (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hΛ) ht)
    exact (mul_le_mul_of_nonneg_right hh hΛ).trans_eq (one_mul _)
  have hc := hExp.comp (LipschitzWith.id.max_const 0).lipschitzOnWith
    (show MapsTo (fun t : ℝ => max t 0) univ (Ici 0) from fun _ _ => le_max_right _ _)
  change LipschitzWith _ (fun t => Real.exp (-Λ*max t 0))
  simpa only [mul_one,Function.comp_def,id_eq] using lipschitzOnWith_univ.mp hc

def coefficient (Λ θ t : ℝ) : ℝ := θ*damping Λ t

theorem continuous_coefficient (Λ θ : ℝ) : Continuous (coefficient Λ θ) :=
  (continuous_damping Λ).const_mul θ

theorem coefficient_bound {Λ : ℝ} (hΛ : 0≤Λ) (θ t : ℝ) : |coefficient Λ θ t|≤|θ| := by
  rw [coefficient,abs_mul,abs_of_pos (damping_pos _ _)]
  exact mul_le_of_le_one_right (abs_nonneg _) (damping_le_one hΛ t)

theorem hasDerivAt_coefficient {Λ θ t : ℝ} (ht : 0<t) :
    HasDerivAt (coefficient Λ θ) (-Λ*coefficient Λ θ t) t := by
  have hh := (hasDerivAt_damping (Λ := Λ) ht).const_mul θ
  change HasDerivAt (fun r => θ*damping Λ r) (-Λ*(θ*damping Λ t)) t
  have he : -Λ*(θ*damping Λ t)=θ*(-Λ*damping Λ t) := by ring
  rw [he]
  exact hh

theorem lipschitz_coefficient {Λ : ℝ} (hΛ : 0≤Λ) (θ : ℝ) :
    LipschitzWith (‖θ‖₊*⟨Λ,hΛ⟩) (coefficient Λ θ) := by
  apply LipschitzWith.of_dist_le_mul
  intro t r
  rw [dist_eq_norm,coefficient,coefficient,← mul_sub,norm_mul]
  exact (mul_le_mul_of_nonneg_left ((lipschitz_damping hΛ).dist_le_mul t r) (norm_nonneg θ)).trans_eq (by
    simp only [NNReal.coe_mul,coe_nnnorm,dist_eq_norm]
    ring)

end SHE.ClippedExponential
