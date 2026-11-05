module

public import SHE.ClippedExponential

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
noncomputable section

namespace SHE.DampedAffineGaussian
open MeasureTheory Set SmoothCylinders GaussianIncrement
open scoped NNReal ENNReal
variable {k n : ℕ}

def linear (Λ θ : ℝ) (P Q : State k→L[ℝ]State n) (t : ℝ) : State k→L[ℝ]State n :=
  P+ClippedExponential.coefficient Λ θ t • Q

def shift (Λ θ : ℝ) (d e : State n) (t : ℝ) : State n :=
  e-ClippedExponential.coefficient Λ θ t • d

def linearDerivative (Λ θ : ℝ) (Q : State k→L[ℝ]State n) (t : ℝ) : State k→L[ℝ]State n :=
  (-Λ*ClippedExponential.coefficient Λ θ t) • Q

def shiftDerivative (Λ θ : ℝ) (d : State n) (t : ℝ) : State n :=
  -((-Λ*ClippedExponential.coefficient Λ θ t) • d)

theorem continuous_linear (Λ θ : ℝ) (P Q : State k→L[ℝ]State n) :
    Continuous (linear Λ θ P Q) :=
  continuous_const.add ((ClippedExponential.continuous_coefficient Λ θ).smul continuous_const)

theorem continuous_shift (Λ θ : ℝ) (d e : State n) : Continuous (shift Λ θ d e) :=
  continuous_const.sub ((ClippedExponential.continuous_coefficient Λ θ).smul continuous_const)

theorem linear_bound {Λ : ℝ} (hΛ : 0≤Λ) (θ : ℝ) (P Q : State k→L[ℝ]State n) (t : ℝ) :
    ‖linear Λ θ P Q t‖≤‖P‖+|θ| * ‖Q‖ := by
  change ‖P+ClippedExponential.coefficient Λ θ t • Q‖≤_
  have hc := ClippedExponential.coefficient_bound hΛ θ t
  calc
    _≤‖P‖+‖ClippedExponential.coefficient Λ θ t • Q‖ := norm_add_le _ _
    _=‖P‖+|ClippedExponential.coefficient Λ θ t| * ‖Q‖ := by rw [norm_smul,Real.norm_eq_abs]
    _≤_ := add_le_add le_rfl (mul_le_mul_of_nonneg_right hc (norm_nonneg Q))

theorem hasDerivAt_linear {Λ θ t : ℝ} (P Q : State k→L[ℝ]State n) (ht : 0<t) :
    HasDerivAt (linear Λ θ P Q) (linearDerivative Λ θ Q t) t := by
  exact ((ClippedExponential.hasDerivAt_coefficient ht).smul_const Q).const_add P

theorem hasDerivAt_shift {Λ θ t : ℝ} (d e : State n) (ht : 0<t) :
    HasDerivAt (shift Λ θ d e) (shiftDerivative Λ θ d t) t := by
  exact ((ClippedExponential.hasDerivAt_coefficient ht).smul_const d).const_sub e

theorem lipschitz_linear {Λ : ℝ} (hΛ : 0≤Λ) (θ : ℝ) (P Q : State k→L[ℝ]State n) :
    ∃ K : ℝ≥0,LipschitzWith K (linear Λ θ P Q) := by
  have hh := ((ContinuousLinearMap.toSpanSingleton ℝ Q).lipschitzWith.comp
    (ClippedExponential.lipschitz_coefficient hΛ θ))
  have hr := (LipschitzWith.const P).add hh
  exact ⟨_,hr⟩

theorem lipschitz_shift {Λ : ℝ} (hΛ : 0≤Λ) (θ : ℝ) (d e : State n) :
    ∃ K : ℝ≥0,LipschitzWith K (shift Λ θ d e) := by
  have hh := ((ContinuousLinearMap.toSpanSingleton ℝ d).lipschitzWith.comp
    (ClippedExponential.lipschitz_coefficient hΛ θ))
  have hr := (LipschitzWith.const e).sub hh
  exact ⟨_,hr⟩

theorem derivative_bound {Λ : ℝ} (hΛ : 0≤Λ) (θ : ℝ) (P Q : State k→L[ℝ]State n) (d : State n) (t : ℝ) :
    ‖linearDerivative Λ θ Q t‖≤Λ*|θ| * (‖Q‖+‖d‖) ∧
    ‖shiftDerivative Λ θ d t‖≤Λ*|θ| * (‖Q‖+‖d‖) := by
  have hc : ‖-Λ*ClippedExponential.coefficient Λ θ t‖≤Λ*|θ| := by
    rw [norm_mul,norm_neg,Real.norm_eq_abs,abs_of_nonneg hΛ,Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (ClippedExponential.coefficient_bound hΛ θ t) hΛ
  constructor
  · exact ((norm_smul _ _).trans_le (mul_le_mul_of_nonneg_right hc (norm_nonneg Q))).trans
      (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (norm_nonneg d)) (by positivity))
  · rw [shiftDerivative,norm_neg]
    exact ((norm_smul _ _).trans_le (mul_le_mul_of_nonneg_right hc (norm_nonneg d))).trans
      (mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (norm_nonneg Q)) (by positivity))

/-- The actual exponentially damped two-block affine mean gives an
admissible localized Gaussian Itô test, with all deterministic test
conditions discharged. The covariance still comes from the physical
coefficient/observation integral. -/
theorem smoothTimeTest (W : ClippedCovariance.ObservationWindow n) (hleft : 0≤W.left)
    {F : State n→ℝ} (hF : BoundedSmooth F) {Λ : ℝ} (hΛ : 0≤Λ) (θ : ℝ)
    (P Q : State k→L[ℝ]State n) (d e : State n) :
    LocalizedItoTest.SmoothTimeTest W.left W.right
      (GaussianAffineFields.value W.path F (linear Λ θ P Q) (shift Λ θ d e))
      (GaussianAffineFields.derivative W F (linear Λ θ P Q) (linearDerivative Λ θ Q)
        (shift Λ θ d e) (shiftDerivative Λ θ d)) := by
  obtain ⟨KL,hL⟩ := lipschitz_linear hΛ θ P Q
  obtain ⟨Km,hm⟩ := lipschitz_shift hΛ θ d e
  apply GaussianAffineFields.smoothTimeTest W hF _ _ _ _
    (by positivity : 0≤‖P‖+|θ| * ‖Q‖) (linear_bound hΛ θ P Q)
    (by positivity : 0≤Λ*|θ| * (‖Q‖+‖d‖)) KL Km hL hm
  · exact ((continuous_const.mul (ClippedExponential.continuous_coefficient Λ θ)).smul continuous_const).measurable
  · exact (((continuous_const.mul (ClippedExponential.continuous_coefficient Λ θ)).smul continuous_const).neg).measurable
  · exact Filter.Eventually.of_forall (fun t ht => hasDerivAt_linear P Q (hleft.trans_lt ht.1))
  · exact Filter.Eventually.of_forall (fun t ht => hasDerivAt_shift d e (hleft.trans_lt ht.1))
  · exact fun t _ => (derivative_bound hΛ θ P Q d t).1
  · exact fun t _ => (derivative_bound hΛ θ P Q d t).2

end SHE.DampedAffineGaussian
