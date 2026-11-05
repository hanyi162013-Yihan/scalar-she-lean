module

public import SHE.PhysicalAssignedTimeTotal
public import SHE.ControlledScoreRates

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1800000
noncomputable section

namespace SHE.MarkedProfileTimeFactors
open Set MeasureTheory Real StoppedFourier CutoffWordLevel CutoffWordHistories CutoffCarriers
  PhysicalScoreChain PhysicalAssignmentGapScale ProfileL2 ControlledScoreRates
open scoped BigOperators
variable {X : Type} [MeasurableSpace X] {R : CutoffWordLevel.ReferenceData} {n : ℕ}

def freshDegree (P : CanonicalCovariance.ProfileParameters) : ℝ := (P.exponent+3)/4

theorem freshDegree_pos (P : CanonicalCovariance.ProfileParameters) : 0<freshDegree P := by
  unfold freshDegree
  linarith [P.exponent_pos]

theorem freshDegree_le_one (P : CanonicalCovariance.ProfileParameters) : freshDegree P≤1 := by
  unfold freshDegree
  linarith [P.exponent_le_one]

def inputConstant (P : CanonicalCovariance.ProfileParameters) (d : CircleL2) (n : ℕ) : ℝ :=
  sharpConstant P d*((n:ℝ)/(P.lower/2))*
    (1+2/(((P.exponent-1)/4)+1))*2^(-((P.exponent-1)/4))

theorem inputConstant_nonneg (P : CanonicalCovariance.ProfileParameters) (d : CircleL2) (n : ℕ) :
    0 ≤ inputConstant P d n := by
  unfold inputConstant
  have hm : 0≤(n:ℝ)/(P.lower/2) :=
    div_nonneg (Nat.cast_nonneg n) (half_pos P.lower_pos).le
  have ha : 0<(P.exponent-1)/4+1 := by linarith [P.exponent_pos]
  have hfactor : 0≤1+2/(((P.exponent-1)/4)+1) := by positivity
  exact mul_nonneg (mul_nonneg (mul_nonneg (sharpConstant_nonneg P d) hm) hfactor)
    (rpow_nonneg (by norm_num) _)

/-- The actual earliest-gap one-input gain has precisely the positive
fresh degree admitted by the checked all-order time simplex. -/
theorem input_gain_identity (P : CanonicalCovariance.ProfileParameters) (d : CircleL2)
    (n : ℕ) {gap : ℝ} (hgap : 0<gap) :
    sharpConstant P d*(((n:ℝ)/(P.lower/2))*(gap/2)^((P.exponent-1)/4)*
      (1+2/(((P.exponent-1)/4)+1)))=
      inputConstant P d n*gap^(freshDegree P-1) := by
  have hpow : (gap/2)^((P.exponent-1)/4)=
      gap^((P.exponent-1)/4)*2^(-((P.exponent-1)/4)) := by
    rw [Real.div_rpow hgap.le (by norm_num),Real.rpow_neg (by norm_num : (0:ℝ)≤2),div_eq_mul_inv]
  rw [hpow]
  rw [show freshDegree P-1=(P.exponent-1)/4 by unfold freshDegree;ring]
  unfold inputConstant
  ring

theorem active_density_identity (L : Level R X n) (P : CanonicalCovariance.ProfileParameters)
    (d : CircleL2) (ell : ℝ) (C : ℕ→ℝ) (k : ℕ) (q A0 ν : ℝ) (p : History X k)
    (hp : PhysicalParentGeometry.StrictHistory L k p) (hq : q<(carrier L k).terminal p) :
    (timeWeight L ell C k p*SharpWordTimeScale.total L P k p q A0 ν)*
      (sharpConstant P d*((((n+k:ℕ):ℝ)/(P.lower/2))*
        (((carrier L k).terminal p-q)/2)^((P.exponent-1)/4)*
          (1+2/(((P.exponent-1)/4)+1))))=
      inputConstant P d (n+k)*totalIntegrand L P ell C k q (freshDegree P) A0 ν p := by
  rw [input_gain_identity P d (n+k) (sub_pos.mpr hq)]
  rw [totalIntegrand,ite_eq_left ⟨hp,hq⟩]
  ring

end SHE.MarkedProfileTimeFactors
