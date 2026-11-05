module

public import SHE.HeatDominatedOperator
public import SHE.HaarNegativeCoarse

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHE.HeatDominatedCoarse
open Finset Set MeasureTheory AddCircle CircleHeat HeatMarkov NegativeNash HaarWeightedHeat FiniteHaar
local instance : Fact (0 < (1:ℝ)) := ⟨zero_lt_one⟩
variable {w K : ℝ} (hw : 0 < w) (hK : 0 ≤ K)
variable (A : CircleL2 →L[ℂ] CircleL2)
variable (k : AddCircle (1:ℝ) × AddCircle (1:ℝ) → ℂ) (hk : Measurable k)
variable (hbound : ∀ x y,‖k (x,y)‖ ≤ K*‖kernel w hw (y-x)‖)
variable (hactual : ∀ f : CircleL2,A f =ᵐ[haarAddCircle]
  (fun x => ∫ y : AddCircle (1:ℝ),k (x,y)*f y ∂haarAddCircle))

include hw hK hk hbound hactual in
/-- Actual localized coarse negative-input/output packet for every
literal heat-dominated operator. The two heat ages stay distinct. -/
theorem packet {Λ ρ t : ℝ} (hΛ : 1 ≤ Λ) (hρ : 0 < ρ) (hρhalf : ρ < 1/2)
    (ht : 0 < t) (p : List Bool) (hcoarse : Real.sqrt t ≤ nodeLength p)
    (v : CircleL2) (hv : ∀ᵐ y ∂haarAddCircle, y ∉ nodeCell p → v y = 0) :
    energy Λ ρ (A (heat t v)) ≤
      HaarNegativeCoarse.constant ρ*K^2*(Λ^ρ+t^(-ρ))*
        min (Λ^(-ρ)) ((((2^(p.length+1):ℕ):ℝ))^(-2*ρ))*energy Λ ρ v := by
  let N : ℝ := ((2^(p.length+1):ℕ):ℝ)
  let T := Λ^ρ+t^(-ρ)
  let E := energy Λ ρ v
  let z := A (heat t v)
  have hN : 0 < N := by dsimp [N]; positivity
  have hT : 0 ≤ T := by dsimp [T]; positivity
  have hE : 0 ≤ E := by dsimp [E,energy]; positivity
  have hC : 0 ≤ HaarNegativeCoarse.constant ρ := zero_le_one.trans (HaarNegativeCoarse.constant_one_le ρ)
  have hL : 0 < NegativeL1Heat.constant ρ := HaarNegativeCoarse.l1Constant_pos hρ hρhalf
  have hz : ‖z‖^2 ≤ K^2*T*E := by
    have hh := HeatDominatedOperator.norm_sq_le hw hK A k hk hbound hactual (heat t v)
    exact hh.trans (mul_le_mul_of_nonneg_left
      (NegativeL2Heat.heat_norm_sq_negative hΛ hρ.le (by linarith : ρ ≤ 1) ht v) (sq_nonneg K) |>.trans_eq (by dsimp only [T,E]; ring))
  have hz1 : normOne z^2 ≤ K^2*NegativeL1Heat.constant ρ*N⁻¹*T*E := by
    have hh := pow_le_pow_left₀ (normOne_nonneg _) (HeatDominatedOperator.normOne_le hw hK A k hk hbound hactual (heat t v)) 2
    rw [mul_pow] at hh
    exact hh.trans ((mul_le_mul_of_nonneg_left
      (NegativeL1Heat.supported_heat_normOne_negative hΛ hρ hρhalf ht p hcoarse v hv) (sq_nonneg K)).trans_eq (by ring))
  have hi := energy_square_bounds hΛ hρ hρhalf
    (by positivity : 0 ≤ K^2*T) (by positivity : 0 ≤ K^2*NegativeL1Heat.constant ρ*N⁻¹*T) hE z hz hz1
  have hi' : energy Λ ρ z ≤ interpolationConstant ρ*(NegativeL1Heat.constant ρ)^(2*ρ)*K^2*T*N^(-2*ρ)*E := by
    apply hi.trans_eq
    rw [Real.mul_rpow (sq_nonneg K) hT,
      Real.mul_rpow (mul_nonneg (mul_nonneg (sq_nonneg K) hL.le) (inv_nonneg.mpr hN.le)) hT,
      Real.mul_rpow (mul_nonneg (sq_nonneg K) hL.le) (inv_nonneg.mpr hN.le),
      Real.mul_rpow (sq_nonneg K) hL.le,Real.inv_rpow hN.le,← Real.rpow_neg hN.le]
    calc
      _ = interpolationConstant ρ*(NegativeL1Heat.constant ρ)^(2*ρ)*N^(-(2*ρ))*
          ((K^2)^(1-2*ρ)*(K^2)^(2*ρ))*(T^(1-2*ρ)*T^(2*ρ))*E := by ring
      _ = _ := by
        rw [← Real.rpow_add' (sq_nonneg K) (by norm_num : (1-2*ρ)+(2*ρ) ≠ 0),
          ← Real.rpow_add' hT (by norm_num : (1-2*ρ)+(2*ρ) ≠ 0),
          show 1-2*ρ+(2*ρ) = 1 by ring,Real.rpow_one,Real.rpow_one]
        ring
  have hm : energy Λ ρ z ≤ Λ^(-ρ)*‖z‖^2 := by
    have hh := CellNegative.energy_mass_le (zero_lt_one.trans_le hΛ) hρ.le z
    rw [Real.rpow_neg (zero_lt_one.trans_le hΛ).le,mul_comm,← div_eq_mul_inv]
    exact (le_div_iff₀ (Real.rpow_pos_of_pos (zero_lt_one.trans_le hΛ) _)).mpr (by simpa only [mul_comm] using! hh)
  have hm' : energy Λ ρ z ≤ HaarNegativeCoarse.constant ρ*K^2*T*Λ^(-ρ)*E := by
    have hh := hm.trans (mul_le_mul_of_nonneg_left hz (by positivity))
    have hh' := mul_le_mul_of_nonneg_right (HaarNegativeCoarse.constant_one_le ρ) (by positivity : 0 ≤ K^2*T*Λ^(-ρ)*E)
    nlinarith only [hh,hh']
  have hi'' : energy Λ ρ z ≤ HaarNegativeCoarse.constant ρ*K^2*T*N^(-2*ρ)*E := by
    have hh := mul_le_mul_of_nonneg_right (le_max_right 1 (interpolationConstant ρ*(NegativeL1Heat.constant ρ)^(2*ρ)))
      (by positivity : 0 ≤ K^2*T*N^(-2*ρ)*E)
    exact hi'.trans (by dsimp only [HaarNegativeCoarse.constant] at *; nlinarith only [hh])
  rw [show HaarNegativeCoarse.constant ρ*K^2*(Λ^ρ+t^(-ρ))*min (Λ^(-ρ)) (N^(-2*ρ))*energy Λ ρ v =
    (HaarNegativeCoarse.constant ρ*K^2*T*E)*min (Λ^(-ρ)) (N^(-2*ρ)) by dsimp only [T,E]; ring,
    mul_min_of_nonneg _ _ (by positivity : 0 ≤ HaarNegativeCoarse.constant ρ*K^2*T*E)]
  exact le_min (hm'.trans_eq (by ring)) (hi''.trans_eq (by ring))

end SHE.HeatDominatedCoarse
