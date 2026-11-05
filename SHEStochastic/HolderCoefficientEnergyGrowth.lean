module

public import SHEStochastic.HolderCoefficientContinuity
public import SHEStochastic.StateNoiseCovariance
public import SHEStochastic.StateDriverCovariance

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section

namespace SHEStochastic.HolderCoefficientEnergyGrowth
open MeasureTheory HolderCoefficientIntegrability
open scoped NNReal ENNReal
variable {E V : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup V] {G : E → V} {C β : ℝ≥0}

/-- Globally sublinear Holder growth gives a linear energy bound. -/
theorem pointwise (hG : HolderWith C β G) (hβ1 : β≤1) (x : E) :
    ‖G x‖^2≤4*(‖G 0‖+(C : ℝ))^2*(1+‖x‖^2) := by
  have hp : ‖x‖^(2*(β : ℝ))≤1+‖x‖^2 := by
    by_cases hx : ‖x‖≤1
    · exact (Real.rpow_le_one (norm_nonneg _) hx (by positivity)).trans (by linarith [sq_nonneg ‖x‖])
    · have hb : (β : ℝ)≤1 := by exact_mod_cast hβ1
      have hh := Real.rpow_le_rpow_of_exponent_le (le_of_not_ge hx)
        (show 2*(β : ℝ)≤(2 : ℝ) by linarith)
      rw [Real.rpow_two] at hh
      linarith
  have hh := UnboundedCoefficientCutoff.squared_growth hG x
  nlinarith [mul_nonneg (sq_nonneg (‖G 0‖+(C : ℝ))) (sub_nonneg.mpr hp)]

variable {X : Type*} [MeasurableSpace X] (ν : Measure X) [IsProbabilityMeasure ν]
    [InnerProductSpace ℝ V] [CompleteSpace V] [MeasurableSpace V] [BorelSpace V]
    [SecondCountableTopology V]

/-- The bound holds for the existing coefficient L2 class of every
L2 state, including unbounded spatial representatives. -/
theorem coefficient_bound (hG : HolderWith C β G) (hβ : 0<β) (hβ1 : β≤1) (u : Lp E 2 ν) :
    ‖coefficient hβ hβ1 hG u‖^2≤4*(‖G 0‖+(C : ℝ))^2*(1+‖u‖^2) := by
  let A : ℝ := 4*(‖G 0‖+(C : ℝ))^2
  have hi : Integrable (fun x => A*(1+‖u x‖^2)) ν :=
    ((integrable_const (1 : ℝ)).add (Lp.memLp u).norm.integrable_sq).const_mul A
  have hp : ∀ᵐ x ∂ν,‖coefficient hβ hβ1 hG u x‖^2≤A*(1+‖u x‖^2) := by
    filter_upwards [coefficient_ae hβ hβ1 hG u] with x hx
    rw [hx]
    exact pointwise hG hβ1 (u x)
  rw [SHE.PredictableL2.realLp_norm_sq]
  apply (integral_mono_ae (Lp.memLp (coefficient hβ hβ1 hG u)).norm.integrable_sq hi hp).trans_eq
  rw [integral_const_mul,integral_add (integrable_const (1 : ℝ)) (Lp.memLp u).norm.integrable_sq,
    integral_const,probReal_univ,one_smul,←SHE.PredictableL2.realLp_norm_sq]

/-- Radial cutoffs obey the identical energy bound at every radius. -/
theorem cutoff_bound (hG : HolderWith C β G) (hβ : 0<β) (hβ1 : β≤1) (R : ℝ≥0) (u : Lp E 2 ν) :
    ‖coefficient hβ hβ1 (UnboundedCoefficientCutoff.holder hG R) u‖^2≤
      4*(‖G 0‖+(C : ℝ))^2*(1+‖u‖^2) := by
  have hh := coefficient_bound ν (UnboundedCoefficientCutoff.holder hG R) hβ hβ1 u
  simpa only [UnboundedCoefficientCutoff.agrees G R (show ‖(0 : E)‖≤(R : ℝ) by simp)] using hh

variable [TopologicalSpace X] [CompactSpace X] [BorelSpace X]

theorem row_bound (hG : HolderWith C β G) (hβ : 0<β) (hβ1 : β≤1)
    (k : C(X,ℝ)) (u : Lp E 2 ν) :
    ‖StateNoiseCovariance.row ν hβ hβ1 hG k u‖^2≤
      (‖k‖^2*(4*(‖G 0‖+(C : ℝ))^2))*(1+‖u‖^2) := by
  have hn := ContinuousKernelLpAction.norm_bound ν (coefficient hβ hβ1 hG u) k
  have hs := pow_le_pow_left₀ (norm_nonneg _) hn 2
  rw [mul_pow] at hs
  exact hs.trans (by
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left
      (coefficient_bound ν hG hβ hβ1 u) (sq_nonneg ‖k‖))

theorem diagonal_bound (hG : HolderWith C β G) (hβ : 0<β) (hβ1 : β≤1)
    (k : C(X,ℝ)) (u : Lp E 2 ν) :
    ‖StateNoiseCovariance.value ν hβ hβ1 hG hG k k u‖≤
      (‖k‖^2*(4*(‖G 0‖+(C : ℝ))^2))*(1+‖u‖^2) := by
  change ‖inner ℝ (StateNoiseCovariance.row ν hβ hβ1 hG k u)
    (StateNoiseCovariance.row ν hβ hβ1 hG k u)‖≤_
  rw [real_inner_self_eq_norm_sq,Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
  exact row_bound ν hG hβ hβ1 k u

theorem mixed_bound (hG : HolderWith C β G) (hβ : 0<β) (hβ1 : β≤1)
    (k : C(X,ℝ)) (b : Lp V 2 ν) (u : Lp E 2 ν) :
    ‖StateDriverCovariance.value ν hβ hβ1 hG k b u‖≤
      (‖k‖^2*(4*(‖G 0‖+(C : ℝ))^2)+‖b‖^2)*(1+‖u‖^2) := by
  let r := StateNoiseCovariance.row ν hβ hβ1 hG k u
  have hr := row_bound ν hG hβ hβ1 k u
  change ‖inner ℝ r b‖≤_
  apply (norm_inner_le_norm r b).trans
  nlinarith [sq_nonneg (‖r‖-‖b‖),sq_nonneg ‖r‖,
    mul_nonneg (sq_nonneg ‖b‖) (sq_nonneg ‖u‖)]

theorem cutoff_diagonal_bound (hG : HolderWith C β G) (hβ : 0<β) (hβ1 : β≤1)
    (R : ℝ≥0) (k : C(X,ℝ)) (u : Lp E 2 ν) :
    ‖StateNoiseCovariance.value ν hβ hβ1 (UnboundedCoefficientCutoff.holder hG R)
      (UnboundedCoefficientCutoff.holder hG R) k k u‖≤
      (‖k‖^2*(4*(‖G 0‖+(C : ℝ))^2))*(1+‖u‖^2) := by
  simpa only [UnboundedCoefficientCutoff.agrees G R (show ‖(0 : E)‖≤(R : ℝ) by simp)] using
    diagonal_bound ν (UnboundedCoefficientCutoff.holder hG R) hβ hβ1 k u

theorem cutoff_mixed_bound (hG : HolderWith C β G) (hβ : 0<β) (hβ1 : β≤1)
    (R : ℝ≥0) (k : C(X,ℝ)) (b : Lp V 2 ν) (u : Lp E 2 ν) :
    ‖StateDriverCovariance.value ν hβ hβ1 (UnboundedCoefficientCutoff.holder hG R) k b u‖≤
      (‖k‖^2*(4*(‖G 0‖+(C : ℝ))^2)+‖b‖^2)*(1+‖u‖^2) := by
  simpa only [UnboundedCoefficientCutoff.agrees G R (show ‖(0 : E)‖≤(R : ℝ) by simp)] using
    mixed_bound ν (UnboundedCoefficientCutoff.holder hG R) hβ hβ1 k b u

end SHEStochastic.HolderCoefficientEnergyGrowth
