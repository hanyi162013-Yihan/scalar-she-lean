module

public import SHE.UncutSmoothWords
public import SHE.UncutRowMass

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section

namespace SHE.UncutHistoryMass
open Set MeasureTheory Filter StoppedFourier WordRecursion
open CutoffWordLevel CutoffWordHistories CutoffCarriers UncutSmoothWords UncutRowMass PhysicalRemainderMass
open Classical
variable {P : Type} [MeasurableSpace P] {R : ReferenceData} {n : ℕ}
variable (L : CutoffWordLevel.Level R P n) (μ : Measure P) [IsFiniteMeasure μ]

def branchMass (k : ℕ) : ℝ := ((n+k : ℕ) : ℝ)*heatMass R.horizon

theorem branchMass_nonneg (k : ℕ) : 0≤branchMass (R := R) (n := n) k :=
  mul_nonneg (Nat.cast_nonneg _) (heatMass_nonneg (R.base_nonneg.trans R.ordered))

/-- Full uncut finite-history integrability is proved by integrating
the true newest spatial row first. No pointwise inverse-gap square
is used as a time majorant. -/
theorem weight_integrable (k : ℕ) : Integrable (weight L k) (historyMeasure R μ k) := by
  induction k with
  | zero => exact integrable_const 1
  | succ k ih =>
    have hm := weight_measurable L (k+1)
    apply (integrable_prod_iff hm.aestronglyMeasurable).mpr
    constructor
    · filter_upwards with p
      exact (row_node_integrable L k p).const_mul (weight L k p)
    · have hdom := ih.const_mul (branchMass (R := R) (n := n) k)
      apply hdom.mono' hm.norm.stronglyMeasurable.integral_prod_right'.aestronglyMeasurable
      filter_upwards with p
      have heq : (∫ z : ℝ×HeatCircle, ‖weight L (k+1) (p,z)‖ ∂nodeMeasure R)=
          weight L k p*(∫ z : ℝ×HeatCircle, ‖row L k (p,z)‖^2 ∂nodeMeasure R) := by
        simp_rw [Real.norm_of_nonneg (weight_nonneg L (k+1) _)]
        change (∫ z : ℝ×HeatCircle, weight L k p*‖row L k (p,z)‖^2 ∂nodeMeasure R)=_
        exact integral_const_mul _ _
      rw [heq,Real.norm_of_nonneg (mul_nonneg (weight_nonneg L k p)
        (integral_nonneg (fun _ => sq_nonneg _)))]
      have hh := mul_le_mul_of_nonneg_left (row_node_mass_le L k p) (weight_nonneg L k p)
      simpa only [branchMass,mul_comm] using hh

theorem integral_weight_succ_le (k : ℕ) :
    (∫ p : History P (k+1), weight L (k+1) p ∂historyMeasure R μ (k+1)) ≤
      branchMass (R := R) (n := n) k*(∫ p : History P k, weight L k p ∂historyMeasure R μ k) := by
  change (∫ p : History P k × (ℝ×HeatCircle), weight L (k+1) p
    ∂(historyMeasure R μ k).prod (nodeMeasure R))≤_
  rw [integral_prod _ (weight_integrable L μ (k+1)),← integral_const_mul]
  apply integral_mono_ae (weight_integrable L μ (k+1)).integral_prod_left
    ((weight_integrable L μ k).const_mul _)
  filter_upwards with p
  change (∫ z : ℝ×HeatCircle, weight L k p*‖row L k (p,z)‖^2 ∂nodeMeasure R)≤_
  rw [integral_const_mul]
  have hh := mul_le_mul_of_nonneg_left (row_node_mass_le L k p) (weight_nonneg L k p)
  simpa only [branchMass,mul_comm] using hh

def massBound : ℕ→ℝ
  | 0 => μ.real Set.univ
  | k+1 => branchMass (R := R) (n := n) k*massBound k

theorem massBound_nonneg (k : ℕ) : 0≤massBound (R := R) (n := n) μ k := by
  induction k with
  | zero => exact measureReal_nonneg
  | succ k ih => exact mul_nonneg (branchMass_nonneg k) ih

/-- An explicit finite-depth uncut history mass. Its constants retain
their depth dependence; this is not an infinite-order word estimate. -/
theorem integral_weight_le (k : ℕ) :
    (∫ p : History P k, weight L k p ∂historyMeasure R μ k)≤massBound (R := R) (n := n) μ k := by
  induction k with
  | zero => simpa only [weight,historyMeasure,massBound,integral_const,smul_eq_mul,mul_one] using
      (le_rfl : μ.real univ≤μ.real univ)
  | succ k ih =>
    exact (integral_weight_succ_le L μ k).trans
      (mul_le_mul_of_nonneg_left ih (branchMass_nonneg k))

end SHE.UncutHistoryMass
