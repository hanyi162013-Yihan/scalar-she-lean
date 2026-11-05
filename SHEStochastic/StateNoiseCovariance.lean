module

public import SHEStochastic.HolderRowCovariance
public import SHEStochastic.HolderCoefficientContinuity
public import Mathlib.Topology.ContinuousMap.Bounded.Normed

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHEStochastic.StateNoiseCovariance
open MeasureTheory Filter HolderCoefficientIntegrability
open scoped ENNReal NNReal

variable {X E V : Type*} [MeasurableSpace X] [TopologicalSpace X] [CompactSpace X] [BorelSpace X]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]
  (ν : Measure X) [IsProbabilityMeasure ν]
  {G K : E → V} {C D β : ℝ≥0} (hβ : 0 < β) (hβ1 : β ≤ 1)
  (hG : HolderWith C β G) (hK : HolderWith D β K)

def row (k : C(X, ℝ)) (u : Lp E 2 ν) : Lp V 2 ν :=
  ContinuousKernelLpAction.operator ν (coefficient hβ hβ1 hG u) k

theorem row_ae (k : C(X, ℝ)) (u : Lp E 2 ν) :
    row ν hβ hβ1 hG k u =ᵐ[ν] fun x ↦ k x • G (u x) := by
  filter_upwards [ContinuousKernelLpAction.operator_ae ν (coefficient hβ hβ1 hG u) k,
    coefficient_ae hβ hβ1 hG u] with x hr hc
  exact hr.trans (congrArg (fun v ↦ k x • v) hc)

theorem row_continuous (k : C(X, ℝ)) : Continuous (row ν hβ hβ1 hG k) :=
  (HolderRowCovariance.continuous_coefficient ν k).comp
    (HolderCoefficientContinuity.continuous ν hβ hβ1 hG)

theorem row_congr (k : C(X, ℝ)) (u : Lp E 2 ν)
    (hagree : ∀ᵐ x ∂ν, G (u x) = K (u x)) :
    row ν hβ hβ1 hG k u = row ν hβ hβ1 hK k u := by
  apply Lp.ext
  filter_upwards [row_ae ν hβ hβ1 hG k u, row_ae ν hβ hβ1 hK k u, hagree] with x hg hk hx
  rw [hg, hk, hx]

def value (k l : C(X, ℝ)) (u : Lp E 2 ν) : ℝ :=
  inner ℝ (row ν hβ hβ1 hG k u) (row ν hβ hβ1 hK l u)

theorem continuous (k l : C(X, ℝ)) : Continuous (value ν hβ hβ1 hG hK k l) :=
  (row_continuous ν hβ hβ1 hG k).inner (row_continuous ν hβ hβ1 hK l)

/-- This continuous state functional is the literal spatial covariance
used by a finite family of scalar Fourier tests. Distinct G,K cover
cross covariances of matrix coefficient rows. -/
theorem integral (k l : C(X, ℝ)) (u : Lp E 2 ν) :
    value ν hβ hβ1 hG hK k l u =
      ∫ x, k x * l x * inner ℝ (G (u x)) (K (u x)) ∂ν := by
  rw [value, row, row, HolderRowCovariance.operator_inner]
  apply integral_congr_ae
  filter_upwards [coefficient_ae hβ hβ1 hG u, coefficient_ae hβ hβ1 hK u] with x hg hk
  rw [hg, hk]

theorem diagonal_congr (k l : C(X, ℝ)) (u : Lp E 2 ν)
    (hagree : ∀ᵐ x ∂ν, G (u x) = K (u x)) :
    value ν hβ hβ1 hG hG k l u = value ν hβ hβ1 hK hK k l u := by
  rw [integral, integral]
  apply integral_congr_ae
  filter_upwards [hagree] with x hx
  rw [hx]

/-- Original and radially truncated canonical covariances coincide
whenever the actual state is within the uniform cutoff. -/
theorem cutoff_agrees (k l : C(X, ℝ)) (R : ℝ≥0) (u : Lp E 2 ν)
    (hu : ∀ᵐ x ∂ν, ‖u x‖ ≤ R) :
    value ν hβ hβ1 (UnboundedCoefficientCutoff.holder hG R)
      (UnboundedCoefficientCutoff.holder hG R) k l u = value ν hβ hβ1 hG hG k l u :=
  diagonal_congr ν hβ hβ1 (UnboundedCoefficientCutoff.holder hG R) hG k l u
    (hu.mono fun _ hx ↦ UnboundedCoefficientCutoff.agrees G R hx)

theorem row_bound (k : C(X, ℝ)) (B : ℝ) (hB : 0 ≤ B) (hb : ∀ x, ‖G x‖ ≤ B) (u : Lp E 2 ν) :
    ‖row ν hβ hβ1 hG k u‖ ≤ ‖k‖ * B := by
  have hc : ‖coefficient hβ hβ1 hG u‖ ≤ B := by
    have he : ∀ᵐ x ∂ν, ‖coefficient hβ hβ1 hG u x‖ ≤ B :=
      (coefficient_ae hβ hβ1 hG u).mono fun x hx ↦ by rw [hx]; exact hb (u x)
    simpa [measureUnivNNReal] using Lp.norm_le_of_ae_bound hB he
  exact (ContinuousKernelLpAction.norm_bound ν (coefficient hβ hβ1 hG u) k).trans
    (mul_le_mul_of_nonneg_left hc (norm_nonneg _))

theorem bound (k l : C(X, ℝ)) (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (ha : ∀ x, ‖G x‖ ≤ A) (hb : ∀ x, ‖K x‖ ≤ B) (u : Lp E 2 ν) :
    ‖value ν hβ hβ1 hG hK k l u‖ ≤ (‖k‖ * A) * (‖l‖ * B) :=
  (norm_inner_le_norm _ _).trans
    (mul_le_mul (row_bound ν hβ hβ1 hG k A hA ha u) (row_bound ν hβ hβ1 hK l B hB hb u)
      (norm_nonneg _) (by positivity))

/-- Bounded coefficients give actual bounded continuous canonical
covariance functionals, ready for the proved kernel-pasting interface. -/
def bounded (k l : C(X, ℝ)) (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (ha : ∀ x, ‖G x‖ ≤ A) (hb : ∀ x, ‖K x‖ ≤ B) : BoundedContinuousFunction (Lp E 2 ν) ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (value ν hβ hβ1 hG hK k l)
    (continuous ν hβ hβ1 hG hK k l) ((‖k‖ * A) * (‖l‖ * B))
    (bound ν hβ hβ1 hG hK k l A B hA hB ha hb)

end SHEStochastic.StateNoiseCovariance
