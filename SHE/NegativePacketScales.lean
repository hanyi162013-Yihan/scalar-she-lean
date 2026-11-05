module

public import SHE.HaarNegativeFine
public import SHE.HaarNegativeCoarse

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section

namespace SHE.NegativePacketScales

theorem fine_mass_mesh {Λ ρ t N : ℝ} (hΛ : 0 < Λ) (hρ : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    (ht : 0 < t) (hN : 0 < N) (hNt : t⁻¹ ≤ N^2) :
    N⁻¹^2*t⁻¹*(Λ+N^2)^ρ*min (Λ^(-ρ)*t^(-(1/2:ℝ))) (t^(ρ-1/2)) ≤
      2*N^(2*ρ-2)*t^(ρ-3/2) := by
  let a := min (Λ^(-ρ)*t^(-(1/2:ℝ))) (t^(ρ-1/2))
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have h1 : Λ^ρ*a ≤ t^(-(1/2:ℝ)) := by
    have hh := mul_le_mul_of_nonneg_left (min_le_left (Λ^(-ρ)*t^(-(1/2:ℝ))) (t^(ρ-1/2))) (Real.rpow_nonneg hΛ.le ρ)
    apply hh.trans_eq
    rw [← mul_assoc,← Real.rpow_add hΛ]
    simp
  have h2 : (N^2)^ρ*a ≤ N^(2*ρ)*t^(ρ-1/2) := by
    rw [← Real.rpow_natCast_mul hN.le]
    norm_num only [Nat.cast_ofNat]
    exact mul_le_mul_of_nonneg_left (min_le_right (Λ^(-ρ)*t^(-(1/2:ℝ))) (t^(ρ-1/2))) (by positivity)
  have htN : t^(-ρ) ≤ N^(2*ρ) := by
    have hh := Real.rpow_le_rpow (inv_nonneg.mpr ht.le) hNt hρ
    rw [Real.inv_rpow ht.le,← Real.rpow_neg ht.le,← Real.rpow_natCast_mul hN.le] at hh
    norm_num only [Nat.cast_ofNat] at hh
    exact hh
  have htN' : t^(-(1/2:ℝ)) ≤ N^(2*ρ)*t^(ρ-1/2) := by
    have hh := mul_le_mul_of_nonneg_right htN (Real.rpow_nonneg ht.le (ρ-1/2))
    rw [← Real.rpow_add ht,show -ρ+(ρ-1/2)=-(1/2:ℝ) by ring] at hh
    exact hh
  have hw := Real.rpow_add_le_add_rpow hΛ.le (sq_nonneg N) hρ hρ1
  have hh := (mul_le_mul_of_nonneg_right hw ha).trans (by
    calc
      (Λ^ρ+(N^2)^ρ)*a = Λ^ρ*a+(N^2)^ρ*a := by ring
      _ ≤ 2*N^(2*ρ)*t^(ρ-1/2) := by nlinarith only [h1,h2,htN'])
  have hh' := mul_le_mul_of_nonneg_left hh (by positivity : 0 ≤ N⁻¹^2*t⁻¹)
  have hh'' : N⁻¹^2*t⁻¹*(Λ+N^2)^ρ*a ≤ N⁻¹^2*t⁻¹*(2*N^(2*ρ)*t^(ρ-1/2)) := by
    simpa only [mul_assoc] using! hh'
  apply hh''.trans_eq
  have hNpow : N⁻¹^2*N^(2*ρ) = N^(2*ρ-2) := by
    rw [inv_pow,← Real.rpow_natCast N 2,← Real.rpow_neg hN.le,← Real.rpow_add hN]
    congr 1
    norm_num
    ring
  have htpow : t⁻¹*t^(ρ-1/2) = t^(ρ-3/2) := by
    rw [← Real.rpow_neg_one,← Real.rpow_add ht]
    congr 1
    ring
  calc
    _ = 2*(N⁻¹^2*N^(2*ρ))*(t⁻¹*t^(ρ-1/2)) := by ring
    _ = _ := by rw [hNpow,htpow]

theorem coarse_mass_mesh {Λ ρ t D : ℝ} (hΛ : 0 < Λ) (hρ : 0 ≤ ρ)
    (ht : 0 < t) (hD : 0 < D) (hc : Real.sqrt t ≤ D⁻¹) :
    (Λ^ρ+t^(-ρ))*min (Λ^(-ρ)) ((2*D)^(-2*ρ))*(2*D) ≤
      4*t^(-ρ)*D^(1-2*ρ) := by
  let a := min (Λ^(-ρ)) ((2*D)^(-2*ρ))
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have h1 : Λ^ρ*a ≤ 1 := by
    have hh := mul_le_mul_of_nonneg_left (min_le_left (Λ^(-ρ)) ((2*D)^(-2*ρ))) (Real.rpow_nonneg hΛ.le ρ)
    exact hh.trans_eq (by rw [← Real.rpow_add hΛ]; simp)
  have h2 : a ≤ D^(-2*ρ) := (min_le_right _ _).trans
    (Real.rpow_le_rpow_of_nonpos hD (by linarith) (by linarith))
  have htd : t ≤ (D⁻¹)^2 := by
    have hh := pow_le_pow_left₀ (Real.sqrt_nonneg t) hc 2
    rwa [Real.sq_sqrt ht.le] at hh
  have hscale : 1 ≤ t^(-ρ)*D^(-2*ρ) := by
    have hh := Real.rpow_le_rpow_of_nonpos ht htd (by linarith : -ρ ≤ 0)
    have he : ((D⁻¹)^2)^(-ρ)*D^(-2*ρ) = 1 := by
      rw [← Real.rpow_natCast_mul (inv_nonneg.mpr hD.le),Real.inv_rpow hD.le,← Real.rpow_neg hD.le,← Real.rpow_add hD]
      norm_num
    have hm := mul_le_mul_of_nonneg_right hh (Real.rpow_nonneg hD.le (-2*ρ))
    rwa [he] at hm
  have hb : (Λ^ρ+t^(-ρ))*a ≤ 2*t^(-ρ)*D^(-2*ρ) := by
    have hh := mul_le_mul_of_nonneg_left h2 (Real.rpow_nonneg ht.le (-ρ))
    nlinarith only [h1,hh,hscale]
  have hh := mul_le_mul_of_nonneg_right hb (by positivity : 0 ≤ 2*D)
  apply hh.trans_eq
  have he : D^(-2*ρ)*D = D^(1-2*ρ) := by
    calc
      _ = D^(-2*ρ)*D^(1:ℝ) := by rw [Real.rpow_one]
      _ = _ := by rw [← Real.rpow_add hD]; congr 1 <;> ring
  calc
    _ = 4*t^(-ρ)*(D^(-2*ρ)*D) := by ring
    _ = _ := by rw [he]

end SHE.NegativePacketScales
