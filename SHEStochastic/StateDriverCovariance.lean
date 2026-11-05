module

public import SHEStochastic.StateNoiseCovarianceStability

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHEStochastic.StateDriverCovariance
open MeasureTheory StateNoiseCovariance
open scoped NNReal ENNReal

variable {X E V : Type*} [MeasurableSpace X] [TopologicalSpace X] [CompactSpace X] [BorelSpace X]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]
  (ν : Measure X) [IsProbabilityMeasure ν]
  {G : E → V} {C β : ℝ≥0} (hβ : 0 < β) (hβ1 : β ≤ 1) (hG : HolderWith C β G)

/-- Cross bracket of one state Fourier noise row with a fixed driver
direction. This is the information required to identify the SAME noise
in a joint state/driver weak limit. -/
def value (k : C(X, ℝ)) (b : Lp V 2 ν) (u : Lp E 2 ν) : ℝ :=
  inner ℝ (row ν hβ hβ1 hG k u) b

theorem continuous (k : C(X, ℝ)) (b : Lp V 2 ν) : Continuous (value ν hβ hβ1 hG k b) :=
  (row_continuous ν hβ hβ1 hG k).inner continuous_const

theorem bound (k : C(X, ℝ)) (b : Lp V 2 ν) (B : ℝ) (hB : 0 ≤ B)
    (hb : ∀ z, ‖G z‖ ≤ B) (u : Lp E 2 ν) :
    ‖value ν hβ hβ1 hG k b u‖ ≤ ‖k‖ * B * ‖b‖ :=
  (norm_inner_le_norm _ _).trans
    (mul_le_mul_of_nonneg_right (row_bound ν hβ hβ1 hG k B hB hb u) (norm_nonneg _))

def bounded (k : C(X, ℝ)) (b : Lp V 2 ν) (B : ℝ) (hB : 0 ≤ B) (hb : ∀ z, ‖G z‖ ≤ B) :
    BoundedContinuousFunction (Lp E 2 ν) ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (value ν hβ hβ1 hG k b)
    (continuous ν hβ hβ1 hG k b) (‖k‖ * B * ‖b‖) (bound ν hβ hβ1 hG k b B hB hb)

theorem difference {K : E → V} {D : ℝ≥0} (hK : HolderWith D β K)
    (k : C(X, ℝ)) (b : Lp V 2 ν) (δ : ℝ) (hδ : 0 ≤ δ)
    (hclose : ∀ z, ‖G z - K z‖ ≤ δ) (u : Lp E 2 ν) :
    ‖value ν hβ hβ1 hG k b u - value ν hβ hβ1 hK k b u‖ ≤ ‖k‖ * δ * ‖b‖ := by
  change ‖inner ℝ (row ν hβ hβ1 hG k u) b - inner ℝ (row ν hβ hβ1 hK k u) b‖ ≤ _
  rw [← inner_sub_left]
  exact (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right
    (StateNoiseCovarianceStability.row_difference ν hβ hβ1 hG hK k δ hδ hclose u) (norm_nonneg _))

end SHEStochastic.StateDriverCovariance
