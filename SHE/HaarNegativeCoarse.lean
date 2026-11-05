module

public import SHE.NegativeL1Heat
public import SHE.NegativeL2Heat

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1800000
noncomputable section

namespace SHE.HaarNegativeCoarse
open Finset Set MeasureTheory AddCircle CircleHeat HeatMarkov NegativeNash HaarWeightedHeat FiniteHaar
open SmoothCellSobolev CoarseCellSobolev CircleFractional
local instance haarNegativeCoarse_periodPos : Fact (0 < (1:ℝ)) := ⟨zero_lt_one⟩

theorem l1Constant_pos {ρ : ℝ} (hρ : 0 < ρ) (hρhalf : ρ < 1/2) : 0 < NegativeL1Heat.constant ρ := by
  have hM := (unitFractionalMass_pos hρ hρhalf).le
  have hd : 0 < 1-2*ρ := by linarith
  unfold NegativeL1Heat.constant coarseConstant fractionalConstant
  positivity

def constant (ρ : ℝ) : ℝ := max 1 (interpolationConstant ρ*(NegativeL1Heat.constant ρ)^(2*ρ))

theorem constant_one_le (ρ : ℝ) : 1 ≤ constant ρ := le_max_left _ _

/-- The true rough-output coarse negative-input packet. Both the
massive gain and the local-cell fractional gain are available uniformly
for every node-supported complex L² input. -/
theorem packet {Λ ρ t : ℝ} (hΛ : 1 ≤ Λ) (hρ : 0 < ρ) (hρhalf : ρ < 1/2)
    (ht : 0 < t) (p : List Bool) (hcoarse : Real.sqrt t ≤ nodeLength p)
    (v : CircleL2) (hv : ∀ᵐ y ∂haarAddCircle, y ∉ nodeCell p → v y = 0)
    (b : CircleL2) (B : ℝ) (hB : 0 ≤ B) (hb : ∀ᵐ y ∂haarAddCircle, ‖b y‖ ≤ B) :
    ‖weightedHeat Λ ρ t hΛ hρ.le b B hb v‖^2 ≤
      constant ρ*B^2*(Λ^ρ+t^(-ρ))*
        min (Λ^(-ρ)) ((((2^(p.length+1):ℕ):ℝ))^(-2*ρ))*energy Λ ρ v := by
  let N : ℝ := ((2^(p.length+1):ℕ):ℝ)
  let T := Λ^ρ+t^(-ρ)
  let E := energy Λ ρ v
  let z := CircleMultiplier.operator b B hb (heat t v)
  have hN : 0 < N := by dsimp [N]; positivity
  have hT : 0 ≤ T := by dsimp [T]; positivity
  have hE : 0 ≤ E := by dsimp [E,energy]; positivity
  have hC : 0 ≤ constant ρ := zero_le_one.trans (constant_one_le ρ)
  have hL : 0 < NegativeL1Heat.constant ρ := l1Constant_pos hρ hρhalf
  have hz : ‖z‖^2 ≤ B^2*T*E := by
    have hh := pow_le_pow_left₀ (norm_nonneg _) (CircleMultiplier.multiply_norm_le b B hb (heat t v)) 2
    rw [mul_pow] at hh
    exact hh.trans (mul_le_mul_of_nonneg_left
      (NegativeL2Heat.heat_norm_sq_negative hΛ hρ.le (by linarith : ρ ≤ 1) ht v) (sq_nonneg B) |>.trans_eq (by dsimp only [T,E]; ring))
  have hz1 : normOne z^2 ≤ B^2*NegativeL1Heat.constant ρ*N⁻¹*T*E := by
    have hh := pow_le_pow_left₀ (normOne_nonneg _) (multiply_normOne_le b B hb (heat t v)) 2
    rw [mul_pow] at hh
    exact hh.trans ((mul_le_mul_of_nonneg_left
      (NegativeL1Heat.supported_heat_normOne_negative hΛ hρ hρhalf ht p hcoarse v hv) (sq_nonneg B)).trans_eq (by ring))
  have hi := energy_square_bounds hΛ hρ hρhalf
    (by positivity : 0 ≤ B^2*T) (by positivity : 0 ≤ B^2*NegativeL1Heat.constant ρ*N⁻¹*T) hE z hz hz1
  have hi' : energy Λ ρ z ≤ interpolationConstant ρ*(NegativeL1Heat.constant ρ)^(2*ρ)*B^2*T*N^(-2*ρ)*E := by
    apply hi.trans_eq
    rw [Real.mul_rpow (sq_nonneg B) hT,
      Real.mul_rpow (mul_nonneg (mul_nonneg (sq_nonneg B) hL.le) (inv_nonneg.mpr hN.le)) hT,
      Real.mul_rpow (mul_nonneg (sq_nonneg B) hL.le) (inv_nonneg.mpr hN.le),
      Real.mul_rpow (sq_nonneg B) hL.le,Real.inv_rpow hN.le,← Real.rpow_neg hN.le]
    calc
      _ = interpolationConstant ρ*(NegativeL1Heat.constant ρ)^(2*ρ)*N^(-(2*ρ))*
          ((B^2)^(1-2*ρ)*(B^2)^(2*ρ))*(T^(1-2*ρ)*T^(2*ρ))*E := by ring
      _ = _ := by
        rw [← Real.rpow_add' (sq_nonneg B) (by norm_num : (1-2*ρ)+(2*ρ) ≠ 0),
          ← Real.rpow_add' hT (by norm_num : (1-2*ρ)+(2*ρ) ≠ 0),
          show 1-2*ρ+(2*ρ) = 1 by ring,Real.rpow_one,Real.rpow_one]
        ring
  have hm : energy Λ ρ z ≤ Λ^(-ρ)*‖z‖^2 := by
    have hh := CellNegative.energy_mass_le (zero_lt_one.trans_le hΛ) hρ.le z
    rw [Real.rpow_neg (zero_lt_one.trans_le hΛ).le,mul_comm,← div_eq_mul_inv]
    exact (le_div_iff₀ (Real.rpow_pos_of_pos (zero_lt_one.trans_le hΛ) _)).mpr (by simpa only [mul_comm] using! hh)
  have hm' : energy Λ ρ z ≤ constant ρ*B^2*T*Λ^(-ρ)*E := by
    have hh := hm.trans (mul_le_mul_of_nonneg_left hz (by positivity))
    have hh' := mul_le_mul_of_nonneg_right (constant_one_le ρ) (by positivity : 0 ≤ B^2*T*Λ^(-ρ)*E)
    nlinarith only [hh,hh']
  have hi'' : energy Λ ρ z ≤ constant ρ*B^2*T*N^(-2*ρ)*E := by
    have hh := mul_le_mul_of_nonneg_right (le_max_right 1 (interpolationConstant ρ*(NegativeL1Heat.constant ρ)^(2*ρ)))
      (by positivity : 0 ≤ B^2*T*N^(-2*ρ)*E)
    exact hi'.trans (by dsimp only [constant] at *; nlinarith only [hh])
  change ‖besselHalf Λ ρ hΛ hρ.le z‖^2 ≤ _
  rw [besselHalf_norm_sq]
  rw [show constant ρ*B^2*(Λ^ρ+t^(-ρ))*min (Λ^(-ρ)) (N^(-2*ρ))*energy Λ ρ v =
    (constant ρ*B^2*T*E)*min (Λ^(-ρ)) (N^(-2*ρ)) by dsimp only [T,E]; ring,
    mul_min_of_nonneg _ _ (by positivity : 0 ≤ constant ρ*B^2*T*E)]
  exact le_min (hm'.trans_eq (by ring)) (hi''.trans_eq (by ring))

end SHE.HaarNegativeCoarse
