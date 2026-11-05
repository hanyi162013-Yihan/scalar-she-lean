module

public import SHE.HaarNegativeConstant
public import SHEStochastic.MatrixCellEntries

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
noncomputable section

namespace SHEStochastic.NegativeConstantOutput
open MeasureTheory SHE SHE.FiniteHaar SHE.CircleHeat SHE.HaarWeightedHeat SHE.DyadicApproximation
open scoped NNReal ENNReal
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local notation "μ" => AddCircle.haarAddCircle (T := (1 : ℝ))

def scale (Λ ρ t : ℝ) : ℝ := Real.sqrt (2 * Λ^ρ * t^(-(1/2 : ℝ)))

theorem scale_nonneg (Λ ρ t : ℝ) : 0 ≤ scale Λ ρ t := Real.sqrt_nonneg _

theorem scale_sq {Λ ρ t : ℝ} (hΛ : 1 ≤ Λ) (ht : 0 < t) :
    scale Λ ρ t ^ 2 = 2 * Λ^ρ * t^(-(1/2 : ℝ)) := by
  exact Real.sq_sqrt (by positivity)

theorem average (z : RealL2) : localAverage 0 (realEmbed z) () = ∫ x, z x ∂μ := by
  rw [MatrixCellEntries.localAverage_integral]
  have he : cellSet 0 () = Set.univ := by
    apply Set.eq_univ_of_forall
    intro y
    change cellIndex 0 y = gridCellEquiv 0 ()
    letI : Subsingleton (ZMod (2^0)) := ZMod.subsingleton_iff.mpr (by norm_num)
    exact Subsingleton.elim _ _
  simp only [pow_zero, Nat.cast_one, one_mul, he, Measure.restrict_univ]

theorem mass {Λ ρ t : ℝ} (hΛ : 1 ≤ Λ) (hρ : 0 ≤ ρ) (ht : 0 < t) (ht1 : t ≤ 1)
    (z : RealL2) :
    |∫ x, z x ∂μ| ≤ scale Λ ρ t * ‖besselHalf Λ ρ hΛ hρ (realEmbed z)‖ := by
  have hP : 1 ≤ t^(-(1/2 : ℝ)) := by
    simpa using Real.rpow_le_rpow_of_nonpos ht ht1 (by norm_num : -(1/2 : ℝ) ≤ 0)
  have hh := localAverage_zero_negative_sq hΛ hρ (realEmbed z)
  rw [average, ← besselHalf_norm_sq (hΛ := hΛ) (hρ := hρ)] at hh
  apply (sq_le_sq₀ (abs_nonneg _) (mul_nonneg (scale_nonneg _ _ _) (norm_nonneg _))).mp
  rw [mul_pow, scale_sq hΛ ht]
  have hm := mul_le_mul_of_nonneg_left hP
    (mul_nonneg (Real.rpow_nonneg (zero_lt_one.trans_le hΛ).le ρ)
      (sq_nonneg ‖besselHalf Λ ρ hΛ hρ (realEmbed z)‖))
  nlinarith only [hh, hm]

theorem output {Λ ρ t : ℝ} (hΛ : 1 ≤ Λ) (hρ : 0 < ρ) (hρhalf : ρ < 1/2)
    (ht : 0 < t) (ht1 : t ≤ 1) (b : CircleL2) (B : ℝ) (hB : 0 < B)
    (hb : ∀ᵐ x ∂μ, ‖b x‖ ≤ B) (z : CircleL2) :
    ‖normalizedConstantOutput Λ ρ t hΛ hρ.le b B hb z‖ ≤
      scale Λ ρ t * ‖besselHalf Λ ρ hΛ hρ.le z‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (scale_nonneg _ _ _) (norm_nonneg _))).mp
  rw [normalizedConstantOutput_sq, mul_pow, scale_sq hΛ ht]
  have hh := mul_le_mul_of_nonneg_left
    (weightedHeat_negative_sq hΛ hρ hρhalf ht ht1 b B hB.le hb z)
    (div_nonneg (Real.rpow_nonneg (zero_lt_one.trans_le hΛ).le ρ) (sq_nonneg B))
  rw [← besselHalf_norm_sq (hΛ := hΛ) (hρ := hρ.le)] at hh
  exact hh.trans_eq (by field_simp)

end SHEStochastic.NegativeConstantOutput
