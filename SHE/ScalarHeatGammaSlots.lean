module

public import SHE.ScalarHeatCompleteGamma
public import SHE.CompleteNoiseEnergy

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
namespace SHE.ScalarHeatGammaSlots
open Set MeasureTheory ProbabilityTheory Real ScalarGaussianSemigroup SmoothCylinders
open scoped NNReal BigOperators
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def slots (g0 g1 : ℝ→ℝ) (z0 z1 m0 m1 : ℝ) (L0 L1 R0 R1 : E) : Fin 6→E:=
  ![g0 z0 • (L0-L1),
    (g0 z0-g0 z1) • L1,
    (g0 z1-g1 z1) • L1,
    -(g0 m0 • (R0-R1)),
    -((g0 m0-g0 m1) • R1),
    -((g0 m1-g1 m1) • R1)]

/-- Exact paired COMPLETE martingale decomposition. The actual and
reference roots are compared separately. The two variance slots remain
explicit; no individual current-minus-reference offset bound is needed. -/
theorem decomposition (g0 g1 : ℝ→ℝ) (z0 z1 m0 m1 : ℝ) (L0 L1 R0 R1 : E) :
    (g0 z0 • L0-g0 m0 • R0)-(g1 z1 • L1-g1 m1 • R1)=
      ∑ i:Fin 6,slots g0 g1 z0 z1 m0 m1 L0 L1 R0 R1 i := by
  simp only [slots,Fin.sum_univ_succ,Fin.isValue,Matrix.cons_val_zero,Matrix.cons_val_succ,Fin.sum_univ_zero,add_zero]
  module

/-- Both literal variance profiles are actual Gaussian-heat smoothings
of the SAME constructed scalar band. -/
theorem heat_band_decomposition (a : ℝ→ℝ) (j : ℕ) (σ0 σ1 : ℝ≥0)
    (z0 z1 m0 m1 : ℝ) (L0 L1 R0 R1 : E) :
    (deriv (heat σ0 (ScalarHeatBands.band a (j+1))) z0 • L0-
      deriv (heat σ0 (ScalarHeatBands.band a (j+1))) m0 • R0)-
    (deriv (heat σ1 (ScalarHeatBands.band a (j+1))) z1 • L1-
      deriv (heat σ1 (ScalarHeatBands.band a (j+1))) m1 • R1)=
      ∑ i:Fin 6,slots (deriv (heat σ0 (ScalarHeatBands.band a (j+1))))
        (deriv (heat σ1 (ScalarHeatBands.band a (j+1)))) z0 z1 m0 m1 L0 L1 R0 R1 i :=
  decomposition _ _ _ _ _ _ _ _ _ _

theorem norm_sum_sq_le (w : Fin 6→E) : ‖∑ i,w i‖^2≤6*(∑ i,‖w i‖^2) := by
  calc
    _≤(∑ i:Fin 6,‖w i‖)^2:=pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2
    _≤_:=by simpa only [Finset.card_univ,Fintype.card_fin,Nat.cast_ofNat] using
      (sq_sum_le_card_mul_sum_sq (s:=Finset.univ) (f:=fun i:Fin 6=>‖w i‖))

/-- A single paired bound includes all six changed slots and therefore
both complete roots; the variance and reference-factor terms cannot
silently disappear. -/
theorem paired_bound (g0 g1 : ℝ→ℝ) (z0 z1 m0 m1 : ℝ) (L0 L1 R0 R1 : E) :
    ‖(g0 z0 • L0-g0 m0 • R0)-(g1 z1 • L1-g1 m1 • R1)‖^2≤
      6*∑ i:Fin 6,‖slots g0 g1 z0 z1 m0 m1 L0 L1 R0 R1 i‖^2 := by
  rw [decomposition]
  exact norm_sum_sq_le _

end SHE.ScalarHeatGammaSlots
