module

public import SHE.HeatDominatedOperator
public import SHE.CellNegative

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHE.HeatDominatedNegative
open MeasureTheory AddCircle CircleHeat HeatMarkov NegativeNash HaarWeightedHeat HeatDominatedOperator
local instance : Fact (0 < (1:ℝ)) := ⟨zero_lt_one⟩

def fractionalConstant (ρ : ℝ) : ℝ := interpolationConstant ρ*HeatL1L2.constant^(1-2*ρ)
def constant (ρ : ℝ) : ℝ := HeatL1L2.constant+fractionalConstant ρ

theorem fractionalConstant_nonneg {ρ : ℝ} (hρhalf : ρ < 1/2) : 0 ≤ fractionalConstant ρ :=
  mul_nonneg (interpolationConstant_nonneg hρhalf) (Real.rpow_nonneg HeatL1L2.constant_pos.le _)

theorem constant_pos {ρ : ℝ} (hρhalf : ρ < 1/2) : 0 < constant ρ :=
  add_pos_of_pos_of_nonneg HeatL1L2.constant_pos (fractionalConstant_nonneg hρhalf)

variable {Λ ρ w K : ℝ} (hΛ : 1 ≤ Λ) (hρ : 0 < ρ) (hρhalf : ρ < 1/2)
variable (hw : 0 < w) (hw1 : w ≤ 1) (hK : 0 ≤ K)
variable (A : CircleL2 →L[ℂ] CircleL2)
variable (k : AddCircle (1:ℝ) × AddCircle (1:ℝ) → ℂ) (hk : Measurable k)
variable (hbound : ∀ x y,‖k (x,y)‖ ≤ K*‖kernel w hw (y-x)‖)
variable (hactual : ∀ f : CircleL2,A f =ᵐ[haarAddCircle]
  (fun x => ∫ y : AddCircle (1:ℝ),k (x,y)*f y ∂haarAddCircle))

include hΛ hρ hρhalf hw1 hK hk hbound hactual in
theorem fractional_bound (f : CircleL2) :
    energy Λ ρ (A f) ≤ fractionalConstant ρ*K^2*w^(ρ-1/2)*normOne f^2 := by
  have hL1 := pow_le_pow_left₀ (normOne_nonneg _) (normOne_le hw hK A k hk hbound hactual f) 2
  rw [mul_pow] at hL1
  have hL2 := norm_sq_le_normOne hw hK A k hk hbound hactual hw1 f
  have hh := energy_square_bounds hΛ hρ hρhalf
    (by positivity [HeatL1L2.constant_pos] : 0 ≤ HeatL1L2.constant*K^2*w^(-(1/2:ℝ)))
    (sq_nonneg K) (sq_nonneg (normOne f)) (A f) hL2 hL1
  apply hh.trans_eq
  rw [Real.mul_rpow (mul_nonneg HeatL1L2.constant_pos.le (sq_nonneg K)) (Real.rpow_nonneg hw.le _),
    Real.mul_rpow HeatL1L2.constant_pos.le (sq_nonneg K),← Real.rpow_mul hw.le]
  have he : (K^2)^(1-2*ρ)*(K^2)^(2*ρ)=K^2 := by
    rw [← Real.rpow_add' (sq_nonneg K) (by linarith : 1-2*ρ+2*ρ ≠ 0),
      show 1-2*ρ+2*ρ=1 by ring,Real.rpow_one]
  have ht : w^((-(1/2:ℝ))*(1-2*ρ))=w^(ρ-1/2) := by congr 1; ring
  calc
    _ = interpolationConstant ρ*HeatL1L2.constant^(1-2*ρ)*w^((-(1/2:ℝ))*(1-2*ρ))*
        ((K^2)^(1-2*ρ)*(K^2)^(2*ρ))*normOne f^2 := by ring
    _ = _ := by rw [he,ht]; unfold fractionalConstant; ring

include hΛ hρ hw1 hK hk hbound hactual in
theorem massive_bound (f : CircleL2) :
    energy Λ ρ (A f) ≤ HeatL1L2.constant*K^2*(Λ^(-ρ)*w^(-(1/2:ℝ)))*normOne f^2 := by
  have hΛ0 := zero_lt_one.trans_le hΛ
  have hp : 0 < Λ^ρ := Real.rpow_pos_of_pos hΛ0 _
  have he : Λ^ρ*Λ^(-ρ)=1 := by rw [← Real.rpow_add hΛ0]; simp
  apply (mul_le_mul_iff_right₀ hp).mp
  calc
    _ ≤ ‖A f‖^2 := CellNegative.energy_mass_le hΛ0 hρ.le (A f)
    _ ≤ HeatL1L2.constant*K^2*w^(-(1/2:ℝ))*normOne f^2 :=
      norm_sq_le_normOne hw hK A k hk hbound hactual hw1 f
    _ = _ := by
      calc
        _ = (Λ^ρ*Λ^(-ρ))*(HeatL1L2.constant*K^2*w^(-(1/2:ℝ))*normOne f^2) := by rw [he,one_mul]
        _ = _ := by ring

include hΛ hρ hρhalf hw1 hK hk hbound hactual in
/-- Actual massive and fractional negative-output gains for every
literal heat-dominated kernel operator. This is the two-scale transport
input; neither Schur nor interpolation estimates remain as hypotheses. -/
theorem negative_bound (f : CircleL2) :
    energy Λ ρ (A f) ≤ constant ρ*K^2*
      min (Λ^(-ρ)*w^(-(1/2:ℝ))) (w^(ρ-1/2))*normOne f^2 := by
  have hC1 : HeatL1L2.constant ≤ constant ρ := by unfold constant; linarith [fractionalConstant_nonneg hρhalf]
  have hC2 : fractionalConstant ρ ≤ constant ρ := by unfold constant; linarith [HeatL1L2.constant_pos]
  have hmass := massive_bound hΛ hρ hw hw1 hK A k hk hbound hactual f
  have hfrac := fractional_bound hΛ hρ hρhalf hw hw1 hK A k hk hbound hactual f
  have hm : energy Λ ρ (A f) ≤ (constant ρ*K^2*normOne f^2)*(Λ^(-ρ)*w^(-(1/2:ℝ))) := by
    have hh := mul_le_mul_of_nonneg_right hC1 (by positivity : 0 ≤ K^2*(Λ^(-ρ)*w^(-(1/2:ℝ)))*normOne f^2)
    exact hmass.trans (by nlinarith only [hh])
  have hf : energy Λ ρ (A f) ≤ (constant ρ*K^2*normOne f^2)*w^(ρ-1/2) := by
    have hh := mul_le_mul_of_nonneg_right hC2 (by positivity : 0 ≤ K^2*w^(ρ-1/2)*normOne f^2)
    exact hfrac.trans (by nlinarith only [hh])
  have hb := le_min hm hf
  rw [← mul_min_of_nonneg _ _ (by positivity [constant_pos hρhalf] : 0 ≤ constant ρ*K^2*normOne f^2)] at hb
  exact hb.trans_eq (by ring)

end SHE.HeatDominatedNegative
