module

public import SHEStochastic.HolderWeightedEnergy
public import SHEStochastic.HeatIncrementRateAlgebra

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHEStochastic.HeatIncrementWeightedRate
open MeasureTheory
open scoped NNReal ENNReal

/-- A deterministic heat-increment estimate after multiplication by an
unbounded Hölder coefficient. Its time exponent (3+β)/4 is below one
for every β<1. Both scalar and matrix-valued coefficients are covered. -/
theorem bound {X E V : Type*} [MeasurableSpace X] [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] [NormedAddCommGroup V]
    {ν : Measure X} {G : E → V} {C β : ℝ≥0} (hG : HolderWith C β G) (hβ1 : β ≤ 1)
    (u : Lp E 2 ν) (h : X → ℝ≥0∞) (hh : AEMeasurable h ν)
    {K t δ : ℝ} (hK : 1 ≤ K) (ht : 0 < t) (ht1 : t ≤ 1) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hcap : ∀ᵐ x ∂ν, h x ≤ ENNReal.ofReal (4 * (K * t ^ (-(1 / 2 : ℝ))) ^ 2))
    (henergy : (∫⁻ x, h x ∂ν) ≤ ENNReal.ofReal (K * δ ^ (1 / 4 : ℝ) * t ^ (-(3 / 4 : ℝ)))) :
    (∫⁻ x, h x * ENNReal.ofReal (‖G (u x)‖ ^ 2) ∂ν) ≤
      ENNReal.ofReal (2 * (‖G 0‖ + (C : ℝ)) ^ 2 * 4 ^ (β : ℝ) * K ^ (1 + (β : ℝ)) *
        δ ^ ((1 - (β : ℝ)) / 4) * t ^ (-(3 + (β : ℝ)) / 4)) *
          (1 + ENNReal.ofReal (‖u‖ ^ 2) ^ (β : ℝ)) := by
  let L : ℝ := 4 * (K * t ^ (-(1 / 2 : ℝ))) ^ 2
  let Q : ℝ := K * δ ^ (1 / 4 : ℝ) * t ^ (-(3 / 4 : ℝ))
  let B : ℝ := 4 ^ (β : ℝ) * K ^ (1 + (β : ℝ)) *
    δ ^ ((1 - (β : ℝ)) / 4) * t ^ (-(3 + (β : ℝ)) / 4)
  let A : ℝ := 2 * (‖G 0‖ + (C : ℝ)) ^ 2
  have hk : 0 < K := by linarith
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hβ : (β : ℝ) ≤ 1 := by exact_mod_cast hβ1
  have hFactor : ENNReal.ofReal L ^ (β : ℝ) * ENNReal.ofReal Q ^ (1 - (β : ℝ)) = ENNReal.ofReal B := by
    calc
      _ = ENNReal.ofReal (L ^ (β : ℝ)) * ENNReal.ofReal (Q ^ (1 - (β : ℝ))) :=
        congrArg₂ (· * ·) (ENNReal.ofReal_rpow_of_nonneg hL β.property)
          (ENNReal.ofReal_rpow_of_nonneg hQ (sub_nonneg.mpr hβ))
      _ = ENNReal.ofReal (L ^ (β : ℝ) * Q ^ (1 - (β : ℝ))) :=
        (ENNReal.ofReal_mul (Real.rpow_nonneg hL (β : ℝ))).symm
      _ = _ := congrArg ENNReal.ofReal (HeatIncrementRateAlgebra.factorization hk ht hδ)
  have hBase : ENNReal.ofReal Q ≤ ENNReal.ofReal B := ENNReal.ofReal_le_ofReal
    (HeatIncrementRateAlgebra.leading_bound hK ht ht1 hδ hδ1 β.property hβ)
  have hBound := HolderWeightedEnergy.bound hG hβ1 u h hh (ENNReal.ofReal L)
    (ENNReal.ofReal Q) hcap henergy
  calc
    _ ≤ ENNReal.ofReal A * (ENNReal.ofReal Q +
        ENNReal.ofReal L ^ (β : ℝ) * (ENNReal.ofReal Q ^ (1 - (β : ℝ)) *
          ENNReal.ofReal (‖u‖ ^ 2) ^ (β : ℝ))) := hBound
    _ = ENNReal.ofReal A * (ENNReal.ofReal Q +
        ENNReal.ofReal B * ENNReal.ofReal (‖u‖ ^ 2) ^ (β : ℝ)) := by rw [← mul_assoc, hFactor]
    _ ≤ ENNReal.ofReal A * (ENNReal.ofReal B +
        ENNReal.ofReal B * ENNReal.ofReal (‖u‖ ^ 2) ^ (β : ℝ)) := by gcongr
    _ = ENNReal.ofReal (A * B) * (1 + ENNReal.ofReal (‖u‖ ^ 2) ^ (β : ℝ)) := by
      have hAB : ENNReal.ofReal (A * B) = ENNReal.ofReal A * ENNReal.ofReal B :=
        ENNReal.ofReal_mul (show 0 ≤ A by dsimp [A]; positivity)
      rw [hAB]
      ring
    _ = _ := by congr 2; dsimp [A, B]; ring

end SHEStochastic.HeatIncrementWeightedRate
