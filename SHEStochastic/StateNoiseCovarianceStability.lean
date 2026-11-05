module

public import SHEStochastic.StateNoiseCovariance

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHEStochastic.StateNoiseCovarianceStability
open MeasureTheory HolderCoefficientIntegrability StateNoiseCovariance
open scoped ENNReal NNReal

variable {X E V : Type*} [MeasurableSpace X] [TopologicalSpace X] [CompactSpace X] [BorelSpace X]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]
  (ν : Measure X) [IsProbabilityMeasure ν]
  {G K : E → V} {C D β : ℝ≥0} (hβ : 0 < β) (hβ1 : β ≤ 1)
  (hG : HolderWith C β G) (hK : HolderWith D β K)

/-- Uniform coefficient approximation gives uniform control of the
actual L2 noise row, independently of the state u. -/
theorem row_difference (k : C(X, ℝ)) (δ : ℝ) (hδ : 0 ≤ δ)
    (hclose : ∀ z, ‖G z - K z‖ ≤ δ) (u : Lp E 2 ν) :
    ‖row ν hβ hβ1 hG k u - row ν hβ hβ1 hK k u‖ ≤ ‖k‖ * δ := by
  let g := coefficient hβ hβ1 hG u
  let h := coefficient hβ hβ1 hK u
  have hd : ‖g - h‖ ≤ δ := by
    have ha : ∀ᵐ x ∂ν, ‖(g - h : Lp V 2 ν) x‖ ≤ δ := by
      filter_upwards [Lp.coeFn_sub g h, coefficient_ae hβ hβ1 hG u,
        coefficient_ae hβ hβ1 hK u] with x hx hg hk
      change ‖(g - h : Lp V 2 ν) x‖ ≤ δ
      rw [hx]
      change ‖g x - h x‖ ≤ δ
      change g x = G (u x) at hg
      change h x = K (u x) at hk
      rw [hg, hk]
      exact hclose (u x)
    simpa [measureUnivNNReal] using Lp.norm_le_of_ae_bound hδ ha
  change ‖ContinuousKernelLpAction.operator ν g k - ContinuousKernelLpAction.operator ν h k‖ ≤ _
  rw [HolderRowCovariance.operator_sub]
  exact (ContinuousKernelLpAction.norm_bound ν (g - h) k).trans
    (mul_le_mul_of_nonneg_left hd (norm_nonneg _))

/-- All mixed Fourier covariance entries converge uniformly when the
bounded coefficient converges uniformly. The output may be any real
Hilbert space, so the same estimate applies to vector noise rows. -/
theorem value_difference (k l : C(X, ℝ)) (A B δ : ℝ)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hδ : 0 ≤ δ)
    (hboundG : ∀ z, ‖G z‖ ≤ A) (hboundK : ∀ z, ‖K z‖ ≤ B)
    (hclose : ∀ z, ‖G z - K z‖ ≤ δ) (u : Lp E 2 ν) :
    ‖value ν hβ hβ1 hG hG k l u - value ν hβ hβ1 hK hK k l u‖ ≤
      ‖k‖ * ‖l‖ * (A + B) * δ := by
  let gk := row ν hβ hβ1 hG k u
  let gl := row ν hβ hβ1 hG l u
  let hk := row ν hβ hβ1 hK k u
  let hl := row ν hβ hβ1 hK l u
  have he : inner ℝ gk gl - inner ℝ hk hl =
      inner ℝ (gk - hk) gl + inner ℝ hk (gl - hl) := by
    rw [inner_sub_left, inner_sub_right]
    ring
  change ‖inner ℝ gk gl - inner ℝ hk hl‖ ≤ _
  rw [he]
  calc
    _ ≤ ‖gk - hk‖ * ‖gl‖ + ‖hk‖ * ‖gl - hl‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_inner_le_norm _ _) (norm_inner_le_norm _ _))
    _ ≤ (‖k‖ * δ) * (‖l‖ * A) + (‖k‖ * B) * (‖l‖ * δ) :=
      add_le_add
        (mul_le_mul (row_difference ν hβ hβ1 hG hK k δ hδ hclose u)
          (row_bound ν hβ hβ1 hG l A hA hboundG u) (norm_nonneg _) (by positivity))
        (mul_le_mul (row_bound ν hβ hβ1 hK k B hB hboundK u)
          (row_difference ν hβ hβ1 hG hK l δ hδ hclose u) (norm_nonneg _) (by positivity))
    _ = _ := by ring

end SHEStochastic.StateNoiseCovarianceStability
