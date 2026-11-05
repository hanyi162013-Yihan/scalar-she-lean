module

public import SHE.NegativePacketScales
public import SHE.ThreeBandSeries

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section

namespace SHE.SeparatedPacketScales

theorem mass_cap {Λ ρ δ w : ℝ} (hΛ : 0 < Λ) (hρ : 0 ≤ ρ)
    (hδ : 0 < δ) (hδw : δ ≤ w) :
    (Λ^ρ+δ^(-ρ))*min (Λ^(-ρ)*w^(-(1/2:ℝ))) (w^(ρ-1/2)) ≤
      2*w^(ρ-1/2)*δ^(-ρ) := by
  have hw : 0 < w := hδ.trans_le hδw
  let a := min (Λ^(-ρ)*w^(-(1/2:ℝ))) (w^(ρ-1/2))
  have h1 : Λ^ρ*a ≤ w^(-(1/2:ℝ)) := by
    have hh := mul_le_mul_of_nonneg_left (min_le_left (Λ^(-ρ)*w^(-(1/2:ℝ))) (w^(ρ-1/2))) (Real.rpow_nonneg hΛ.le ρ)
    exact hh.trans_eq (by rw [← mul_assoc,← Real.rpow_add hΛ]; simp)
  have h2 : δ^(-ρ)*a ≤ δ^(-ρ)*w^(ρ-1/2) :=
    mul_le_mul_of_nonneg_left (min_le_right _ _) (Real.rpow_nonneg hδ.le _)
  have hs : w^(-(1/2:ℝ)) ≤ δ^(-ρ)*w^(ρ-1/2) := by
    have hh := mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow_of_nonpos hδ hδw (by linarith : -ρ ≤ 0)) (Real.rpow_nonneg hw.le (ρ-1/2))
    rw [← Real.rpow_add hw,show -ρ+(ρ-1/2)=-(1/2:ℝ) by ring] at hh
    exact hh
  nlinarith only [h1,h2,hs]

theorem fine_mass_mesh {Λ ρ δ w N : ℝ} (hΛ : 0 < Λ) (hρ : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    (hδ : 0 < δ) (hδw : δ ≤ w) (hN : 0 < N) (hNδ : δ⁻¹ ≤ N^2) :
    N⁻¹^2*δ⁻¹*(Λ+N^2)^ρ*min (Λ^(-ρ)*w^(-(1/2:ℝ))) (w^(ρ-1/2)) ≤
      2*N^(2*ρ-2)*δ⁻¹*w^(ρ-1/2) := by
  have hw : 0 < w := hδ.trans_le hδw
  have hNw : w⁻¹ ≤ N^2 := by
    have hh := one_div_le_one_div_of_le hδ hδw
    simp only [one_div] at hh
    exact hh.trans hNδ
  have hh := NegativePacketScales.fine_mass_mesh hΛ hρ hρ1 hw hN hNw
  have hm := mul_le_mul_of_nonneg_left hh (by positivity : 0 ≤ δ⁻¹*w)
  have he : w*w^(ρ-3/2) = w^(ρ-1/2) := by
    calc
      _ = w^(1:ℝ)*w^(ρ-3/2) := by rw [Real.rpow_one]
      _ = _ := by rw [← Real.rpow_add hw]; congr 1; ring
  have hleft : δ⁻¹*w*(N⁻¹^2*w⁻¹*(Λ+N^2)^ρ*min (Λ^(-ρ)*w^(-(1/2:ℝ))) (w^(ρ-1/2))) =
      N⁻¹^2*δ⁻¹*(Λ+N^2)^ρ*min (Λ^(-ρ)*w^(-(1/2:ℝ))) (w^(ρ-1/2)) := by field_simp
  rw [hleft] at hm
  exact hm.trans_eq (by calc
    _ = 2*N^(2*ρ-2)*δ⁻¹*(w*w^(ρ-3/2)) := by ring
    _ = _ := by rw [he])

end SHE.SeparatedPacketScales
