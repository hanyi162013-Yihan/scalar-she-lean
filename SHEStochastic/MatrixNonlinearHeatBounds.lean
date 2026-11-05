module

public import SHEStochastic.MatrixNemytskii
public import SHEStochastic.MatrixFactorHeatStability
public import SHEStochastic.MatrixAnalyticKernel

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
noncomputable section

namespace SHEStochastic.MatrixNonlinearHeatBounds
open MeasureTheory SHE MatrixInfiniteHaar MatrixNemytskii MatrixProfileHilbert NativeHeatObservation
open scoped NNReal ENNReal Matrix.Norms.L2Operator
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by simp⟩
variable {d X : Type*} [Fintype d] [DecidableEq d] [MeasurableSpace X]
local instance : SecondCountableTopology (Physical (d := d)) := Lp.SecondCountableTopology
local instance : MeasurableSpace (Physical (d := d)) := borel _
local instance : BorelSpace (Physical (d := d)) := ⟨rfl⟩

variable (G : MatrixNonlinearCoefficient.Coefficient d)
    (u v : X → Physical (d := d)) (hu : StronglyMeasurable u) (hv : StronglyMeasurable v)

/-- The Frobenius profile distance of the actual nonlinear covariances
is controlled by the vector spatial L2 distance. -/
theorem profile_difference {L : ℝ}
    (hLip : ∀ z w, ‖G.value z-G.value w‖ ≤ L*‖z-w‖) (p : X) :
    ‖MatrixColumnComparison.difference (profile G v hv p) (profile G u hu p)‖ ≤
      (‖toVector d‖*(2*(G.bound : ℝ)*L))*‖u p-v p‖ := by
  change ‖realize d (profile G u hu p)-realize d (profile G v hv p)‖ ≤ _
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [Lp.coeFn_sub (realize d (profile G u hu p)) (realize d (profile G v hv p)),
    realize_ae d (profile G u hu p),realize_ae d (profile G v hv p),
    state_ae u hu p,state_ae v hv p,Lp.coeFn_sub (u p) (v p)] with x hs hpu hpv hsu hsv huv
  rw [hs,Pi.sub_apply,hpu,hpv,← map_sub]
  change ‖toVector d (G.covariance (state u hu (p,x))-G.covariance (state v hv (p,x)))‖ ≤ _
  rw [hsu,hsv,huv,Pi.sub_apply]
  exact ((toVector d).le_opNorm _).trans
    ((mul_le_mul_of_nonneg_left (G.covariance_holder (β := 1) (K := L)
      (by simpa only [Real.rpow_one] using hLip) (u p x) (v p x))
      (norm_nonneg (toVector d))).trans_eq (by rw [Real.rpow_one]; ring))

def factorConstant : ℝ :=
  MatrixFactorHeatStability.constant (G.profile (fun _ => 0) measurable_const)
    (G.profile (fun _ => 0) measurable_const)

theorem factorConstant_nonneg : 0 ≤ factorConstant G := MatrixFactorHeatStability.constant_nonneg _ _

def constant (L : ℝ) : ℝ :=
  factorConstant G*timeScale^(1/2 : ℝ)*(‖toVector d‖*(2*(G.bound : ℝ)*L))^2

theorem constant_nonneg (L : ℝ) : 0 ≤ constant G L :=
  mul_nonneg (mul_nonneg (factorConstant_nonneg G) (Real.rpow_nonneg timeScale_pos.le _)) (sq_nonneg _)

/-- Uniform short-age Lipschitz heat energy for the actual infinite
matrix Haar nonlinearity. The constant depends only on the fixed
coefficient bounds, dimension and Lipschitz constant. -/
theorem bound {L t : ℝ} (hL : 0 ≤ L)
    (hLip : ∀ z w, ‖G.value z-G.value w‖ ≤ L*‖z-w‖)
    (ht : 0 < t) (ht1 : t ≤ 1) (p : X) :
    ‖MatrixAnalyticKernel.kernel t (profile G u hu p)-
      MatrixAnalyticKernel.kernel t (profile G v hv p)‖^2 ≤
      constant G L*t^(-(1/2 : ℝ))*‖u p-v p‖^2 := by
  have hc : 1 ≤ timeScale := by unfold timeScale; nlinarith [Real.one_le_pi_div_two]
  have hb := MatrixFactorHeatStability.bound (div_pos ht timeScale_pos)
    ((div_le_one timeScale_pos).mpr (ht1.trans hc)) (profile G v hv p) (profile G u hu p)
  have heq : MatrixFactorHeatStability.constant (profile G v hv p) (profile G u hu p)=
      factorConstant G := by rfl
  rw [heq,NativeSignedClock.div_neg_rpow ht.le] at hb
  have hp := pow_le_pow_left₀ (norm_nonneg _)
    (profile_difference G u v hu hv hLip p) 2
  have hm := mul_le_mul_of_nonneg_left hp
    (mul_nonneg (factorConstant_nonneg G)
      (mul_nonneg (Real.rpow_nonneg ht.le (-(1/2 : ℝ)))
        (Real.rpow_nonneg timeScale_pos.le (1/2 : ℝ))))
  unfold MatrixAnalyticKernel.kernel
  exact (hb.trans hm).trans_eq (by unfold constant; ring)

end SHEStochastic.MatrixNonlinearHeatBounds
