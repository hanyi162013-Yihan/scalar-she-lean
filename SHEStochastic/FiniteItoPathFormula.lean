module

public import SHEStochastic.PathTaylorRemainder

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
noncomputable section

namespace SHEStochastic.FiniteItoPathFormula
open Filter Set SHE.GaussianTaylor MathFin.QuadraticVariationL2
open scoped NNReal Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def timeSum (H : ℝ≥0) (G : ℝ≥0 → E → ℝ) (x : ℝ≥0 → E) (m : ℕ) : ℝ :=
  ∑ k : Fin m, (G (unifPart H m (k + 1)) (x (unifPart H m (k + 1))) -
    G (unifPart H m k) (x (unifPart H m (k + 1))))

def linearSum (H : ℝ≥0) (G : ℝ≥0 → E → ℝ) (x : ℝ≥0 → E) (m : ℕ) : ℝ :=
  ∑ k : Fin m, fderiv ℝ (G (unifPart H m k)) (x (unifPart H m k))
    (x (unifPart H m (k + 1)) - x (unifPart H m k))

def quadraticSum (H : ℝ≥0) (G : ℝ≥0 → E → ℝ) (x : ℝ≥0 → E) (m : ℕ) : ℝ :=
  ∑ k : Fin m, hessian (G (unifPart H m k)) (x (unifPart H m k))
    (x (unifPart H m (k + 1)) - x (unifPart H m k)) (x (unifPart H m (k + 1)) - x (unifPart H m k))

def remainderSum (H : ℝ≥0) (G : ℝ≥0 → E → ℝ) (x : ℝ≥0 → E) (m : ℕ) : ℝ :=
  ∑ k : Fin m, SecondOrderTaylor.remainder (G (unifPart H m k))
    (x (unifPart H m k)) (x (unifPart H m (k + 1)))

/-- An exact discrete identity; no stochastic or differentiability
hypothesis is used in its algebra. -/
theorem discrete (H : ℝ≥0) (G : ℝ≥0 → E → ℝ) (x : ℝ≥0 → E) (m : ℕ) (hm : 0 < m) :
    G H (x H) - G 0 (x 0) = timeSum H G x m + linearSum H G x m +
      (1 / 2 : ℝ) * quadraticSum H G x m + remainderSum H G x m := by
  have ht : (∑ k : Fin m, (G (unifPart H m (k + 1)) (x (unifPart H m (k + 1))) -
      G (unifPart H m k) (x (unifPart H m k)))) = G H (x H) - G 0 (x 0) := by
    rw [Fin.sum_univ_eq_sum_range (fun k : ℕ ↦ G (unifPart H m (k + 1)) (x (unifPart H m (k + 1))) -
      G (unifPart H m k) (x (unifPart H m k))), Finset.sum_range_sub (fun k ↦ G (unifPart H m k) (x (unifPart H m k)))]
    have hm0 : (m : ℝ≥0) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
    simp [unifPart, hm0]
  rw [← ht]
  simp only [timeSum, linearSum, quadraticSum, remainderSum, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  dsimp [SecondOrderTaylor.remainder]
  ring

variable [ProperSpace E]

/-- The full time-dependent C² path calculus follows once the linear,
quadratic and ordinary time sums have their limits. -/
theorem of_tendsto (H : ℝ≥0) (G : ℝ≥0 → E → ℝ)
    (hG : ∀ t, ContDiff ℝ 2 (G t))
    (hH : Continuous (fun p : ℝ≥0 × E ↦ hessian (G p.1) p.2))
    (x : ℝ≥0 → E) (hx : ContinuousOn x (Icc 0 H)) (ν : ℕ → ℕ)
    (hν : Tendsto ν atTop atTop) {A I Q B : ℝ}
    (htime : Tendsto (fun k ↦ timeSum H G x (ν k)) atTop (𝓝 A))
    (hlinear : Tendsto (fun k ↦ linearSum H G x (ν k)) atTop (𝓝 I))
    (hquadratic : Tendsto (fun k ↦ quadraticSum H G x (ν k)) atTop (𝓝 Q))
    (hbound : ∀ᶠ k in atTop, ∑ j : Fin (ν k),
      ‖x (unifPart H (ν k) (j + 1)) - x (unifPart H (ν k) j)‖ ^ 2 ≤ B) :
    G H (x H) - G 0 (x 0) = A + I + (1 / 2 : ℝ) * Q := by
  have hb : ∀ᶠ k in atTop, ∑ j ∈ Finset.range (ν k),
      ‖x (unifPart H (ν k) (j + 1)) - x (unifPart H (ν k) j)‖ ^ 2 ≤ B := by
    filter_upwards [hbound] with k hk
    rwa [Fin.sum_univ_eq_sum_range (fun j : ℕ ↦
      ‖x (unifPart H (ν k) (j + 1)) - x (unifPart H (ν k) j)‖ ^ 2)] at hk
  have hr : Tendsto (fun k ↦ remainderSum H G x (ν k)) atTop (𝓝 (0 : ℝ)) := by
    have hh := PathTaylorRemainder.tendsto H G hG hH hx hν hb
    have he (k : ℕ) : remainderSum H G x (ν k) = ∑ j ∈ Finset.range (ν k),
        SecondOrderTaylor.remainder (G (unifPart H (ν k) j)) (x (unifPart H (ν k) j))
          (x (unifPart H (ν k) (j + 1))) :=
      Fin.sum_univ_eq_sum_range (fun j : ℕ ↦ SecondOrderTaylor.remainder (G (unifPart H (ν k) j))
        (x (unifPart H (ν k) j)) (x (unifPart H (ν k) (j + 1)))) (ν k)
    simpa only [he] using hh
  have htotal := ((htime.add hlinear).add (hquadratic.const_mul (1 / 2 : ℝ))).add hr
  have hconst : (fun k ↦ timeSum H G x (ν k) + linearSum H G x (ν k) +
      (1 / 2 : ℝ) * quadraticSum H G x (ν k) + remainderSum H G x (ν k)) =ᶠ[atTop]
      (fun _ ↦ G H (x H) - G 0 (x 0)) := by
    filter_upwards [hν.eventually (eventually_gt_atTop 0)] with k hk
    exact (discrete H G x (ν k) hk).symm
  simpa only [add_zero] using tendsto_nhds_unique (tendsto_const_nhds (x := G H (x H) - G 0 (x 0)))
    (htotal.congr' hconst)

end SHEStochastic.FiniteItoPathFormula
