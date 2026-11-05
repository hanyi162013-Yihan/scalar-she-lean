module

public import SHE.VectorRootClips

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1700000
noncomputable section

namespace SHE.VectorFiniteDifferences
variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The distinguished actual current increment is fractionalized while
every old root Bernstein clip remains intact. Only a finite Fréchet jet
through the combined block order is used. -/
theorem paired_mixed_bound_finite (f : E → F) (zs : List E)
    {A ν χ : ℝ} (hA : 0 ≤ A) (hν : 0 ≤ ν) (hχ0 : 0 ≤ χ) (hχ1 : χ ≤ 1)
    (hf : ContDiff ℝ (zs.length+1) f)
    (hb : ∀ j, j ≤ zs.length+1 → ∀ x, ‖iteratedFDeriv ℝ j f x‖ ≤ A*ν^j)
    (e x : E) :
    ‖mixed (e::zs) f x‖ ≤ (2 : ℝ)^(zs.length+1)*A*
      (min 1 (ν*‖e‖))^χ*clips ν zs := by
  have hc0 : 0 ≤ min 1 (ν*‖e‖) := le_min (by norm_num) (mul_nonneg hν (norm_nonneg e))
  have hc1 : min 1 (ν*‖e‖) ≤ 1 := min_le_left _ _
  have hw : min 1 (ν*‖e‖) ≤ (min 1 (ν*‖e‖))^χ := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_ge' hc0 hc1 hχ0 hχ1
  have hh := mixed_clipped_bound_finite (zs.length+1) E F f (e::zs) (by simp) hA hν hf hb x
  simp only [List.length_cons,clips,List.map_cons,List.prod_cons] at hh
  change ‖mixed (e::zs) f x‖ ≤ (2 : ℝ)^(zs.length+1)*A*
    (min 1 (ν*‖e‖)*clips ν zs) at hh
  have hm := mul_le_mul_of_nonneg_left hw
    (show 0 ≤ (2 : ℝ)^(zs.length+1)*A*clips ν zs from
      mul_nonneg (mul_nonneg (by positivity) hA) (clips_nonneg hν zs))
  nlinarith only [hh,hm]

/-- Old translation differences commute with the distinguished genuine
current mean shift; no derivative of a rough coefficient is taken. -/
theorem mixed_current_difference (zs : List E) (e : E) (f : E → F) :
    mixed zs (fun x => f (x+e)-f x) = mixed (e::zs) f := by
  induction zs with
  | nil => rfl
  | cons z zs ih =>
    funext x
    change mixed zs (fun y => f (y+e)-f y) (x+z) -
      mixed zs (fun y => f (y+e)-f y) x = _
    rw [ih]
    change (mixed zs f (x+z+e)-mixed zs f (x+z)) -
      (mixed zs f (x+e)-mixed zs f x) =
      (mixed zs f (x+e+z)-mixed zs f (x+e)) -
        (mixed zs f (x+z)-mixed zs f x)
    rw [show x+z+e=x+e+z by abel]
    abel

end SHE.VectorFiniteDifferences
