module

public import SHE.GaussianNegativePacket

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section

namespace SHE.GaussianPacketOutput
open MeasureTheory Set AddCircle CircleHeat FiniteHaar HeatMarkov NegativeNash HaarWeightedHeat
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩

def constant (ρ : ℝ) : ℝ :=
  (GaussianNegativePacket.constant ρ + GaussianNegativePacket.traceConstant) * localConstant ^ 2

theorem constant_nonneg {ρ : ℝ} (hρhalf : ρ < 1/2) : 0 ≤ constant ρ := by
  have hG := (HeatTrace.fractionalGaussianIntegral_pos hρhalf).le
  have hT := GaussianNegativePacket.traceConstant_pos.le
  unfold constant GaussianNegativePacket.constant
  positivity

/-- A common Gaussian packet theorem for scalar and matrix Haar
derivatives. A proved centered-row amplitude passes through any rough
bounded output multiplier, retaining both massive and fractional gains. -/
theorem negative {Λ ρ t A : ℝ} (hΛ : 1 ≤ Λ) (hρ : 0 < ρ) (hρhalf : ρ < 1/2)
    (ht : 0 < t) (ht1 : t ≤ 1) (hA : 0 ≤ A) (p : List Bool) (v : CircleL2)
    (hpoint : ∀ᵐ x ∂haarAddCircle, ‖heat t v x‖ ≤ A *
      (NodeKernelLocal.constant p t ht x / (((2^(p.length+1):ℕ):ℝ))))
    (b : CircleL2) (B : ℝ) (hB : 0 ≤ B) (hb : ∀ᵐ x ∂haarAddCircle, ‖b x‖ ≤ B) :
    ‖weightedHeat Λ ρ t hΛ hρ.le b B hb v‖ ^ 2 ≤
      constant ρ * A ^ 2 * B ^ 2 * ((((2^(p.length+1):ℕ):ℝ))⁻¹) ^ 2 * t⁻¹ *
        min (Λ^(-ρ)*t^(-(1/2 : ℝ))) (t^(ρ-1/2)) := by
  let N : ℝ := ((2^(p.length+1):ℕ):ℝ)
  let R := A*B*localConstant/(Real.sqrt t*N)
  let z := CircleMultiplier.operator b B hb (heat t v)
  let C := GaussianNegativePacket.constant ρ + GaussianNegativePacket.traceConstant
  have hR : 0 ≤ R := by dsimp [R]; positivity [localConstant_pos]
  have hdom : ∀ᵐ x ∂haarAddCircle, ‖z x‖ ≤ R*‖kernel (8*t) (by positivity) (x-nodeCenter p)‖ := by
    filter_upwards [CircleMultiplier.operator_ae b B hb (heat t v), hb, hpoint] with x hx hbx hpx
    rw [hx, norm_mul]
    exact (mul_le_mul hbx hpx (norm_nonneg _) hB).trans_eq (by
      dsimp only [NodeKernelLocal.constant, R, N, localConstant]
      field_simp)
  have hn := GaussianNegativePacket.dominated_negative hΛ hρ hρhalf ht ht1 hR (nodeCenter p) z hdom
  have hC1 : GaussianNegativePacket.constant ρ ≤ C := by
    dsimp [C]; linarith [GaussianNegativePacket.traceConstant_pos]
  have hC2 : GaussianNegativePacket.traceConstant ≤ C := by
    dsimp [C, GaussianNegativePacket.constant]
    linarith [(HeatTrace.fractionalGaussianIntegral_pos hρhalf).le, GaussianNegativePacket.traceConstant_pos]
  have hc1 : energy Λ ρ z ≤ C*R^2*t^(ρ-1/2) := by
    have hh := mul_le_mul_of_nonneg_right hC1 (mul_nonneg (Real.rpow_nonneg ht.le (ρ-1/2)) (sq_nonneg R))
    exact hn.1.trans (by nlinarith only [hh])
  have hc2 : energy Λ ρ z ≤ C*R^2*(Λ^(-ρ)*t^(-(1/2 : ℝ))) := by
    have hh := mul_le_mul_of_nonneg_right hC2 (by positivity : 0 ≤ Λ^(-ρ)*t^(-(1/2 : ℝ))*R^2)
    exact hn.2.trans (by nlinarith only [hh])
  have hC : 0 ≤ C := GaussianNegativePacket.traceConstant_pos.le.trans hC2
  have hh : energy Λ ρ z ≤ C*R^2*min (Λ^(-ρ)*t^(-(1/2 : ℝ))) (t^(ρ-1/2)) := by
    rw [mul_min_of_nonneg _ _ (mul_nonneg hC (sq_nonneg R))]
    exact le_min hc2 hc1
  change ‖besselHalf Λ ρ hΛ hρ.le z‖^2 ≤ _
  rw [besselHalf_norm_sq]
  apply hh.trans_eq
  have he : R ^ 2 = A ^ 2 * B ^ 2 * localConstant ^ 2 * N⁻¹ ^ 2 * t⁻¹ := by
    dsimp only [R]
    rw [div_pow, mul_pow, mul_pow, mul_pow, Real.sq_sqrt ht.le]
    field_simp
  rw [he]
  dsimp only [C, constant, N]
  ring

end SHE.GaussianPacketOutput
