module

public import SHE.GaussianPacketOutput

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section

namespace SHE.FiniteHaar
open Finset Set MeasureTheory AddCircle CircleHeat HeatMarkov HaarWeightedHeat CellNegative NegativeNash
local instance haarNegativeFine_periodPos : Fact (0 < (1:ℝ)) := ⟨zero_lt_one⟩

theorem rowPacketConstant_nonneg (m U : ℝ) (hm : 0 < m) (j : ℕ) (ρ : ℝ) :
    0 ≤ rowPacketConstant m U hm j ρ := by
  unfold rowPacketConstant rowSlotConstant
  exact mul_nonneg (mul_nonneg (stateJetBound_nonneg _ _ _ _)
    ((Real.sqrt_nonneg _).trans (le_max_left _ _))) (by positivity)

def negativeFineConstant (m U : ℝ) (hm : 0 < m) (j : ℕ) (ρ : ℝ) : ℝ :=
  (GaussianNegativePacket.constant ρ+GaussianNegativePacket.traceConstant)*
    (rowPacketConstant m U hm j ρ)^2*localConstant^2

/-- The actual higher derivative fine packet with a rough bounded output
multiplier. Both massive and fractional gains are retained before the
uniform mass/mesh cancellation. -/
theorem globalHaarColumn_jet_fine_negative {Λ ρ t : ℝ} (hΛ : 1 ≤ Λ)
    (hρ : 0 < ρ) (hρhalf : ρ < 1/2) (ht : 0 < t) (ht1 : t ≤ 1)
    (p : List Bool) (hsmall : nodeLength p ≤ Real.sqrt t) (f : DyadicApproximation.RealL2)
    (m U : ℝ) (hm : 0 < m)
    (hf : ∀ᵐ y ∂haarAddCircle, m ≤ (DyadicApproximation.realEmbed f y).re ∧
      (DyadicApproximation.realEmbed f y).re ≤ U)
    (j : ℕ) (v : Fin (j+1) → DyadicApproximation.RealL2) (M : Fin (j+1) → ℝ)
    (hM : ∀ i, 0 ≤ M i)
    (hv : ∀ i, i ≠ 0 → ∀ᵐ y ∂haarAddCircle, ‖DyadicApproximation.realEmbed (v i) y‖ ≤ M i)
    (b : CircleL2) (B : ℝ) (hB : 0 ≤ B) (hb : ∀ᵐ y ∂haarAddCircle, ‖b y‖ ≤ B) :
    ‖weightedHeat Λ ρ t hΛ hρ.le b B hb
      (iteratedFDeriv ℝ (j+1) (globalHaarColumn (some p)) (DyadicApproximation.realEmbed f)
        (fun i => DyadicApproximation.realEmbed (v i)))‖^2 ≤
      negativeFineConstant m U hm j ρ*B^2*
        ((((2^(p.length+1):ℕ):ℝ))⁻¹)^2*t⁻¹*(Λ+(((2^(p.length+1):ℕ):ℝ))^2)^ρ*
        min (Λ^(-ρ)*t^(-(1/2:ℝ))) (t^(ρ-1/2))*
        localNegativeNorm p Λ ρ hΛ hρ.le (DyadicApproximation.realEmbed (v 0))^2*
        (∏ i ∈ univ.erase (0 : Fin (j+1)), M i)^2 := by
  let A := rowPacketConstant m U hm j ρ * scale Λ ρ (p.length+1) *
    localNegativeNorm p Λ ρ hΛ hρ.le (DyadicApproximation.realEmbed (v 0)) *
      (∏ i ∈ univ.erase (0 : Fin (j+1)), M i)
  have hA : 0 ≤ A := by
    have ha := rowPacketConstant_nonneg m U hm j ρ
    have hH : 0 ≤ localNegativeNorm p Λ ρ hΛ hρ.le (DyadicApproximation.realEmbed (v 0)) :=
      add_nonneg (norm_nonneg _) (norm_nonneg _)
    have hP := prod_nonneg (fun i (_ : i ∈ univ.erase (0 : Fin (j+1))) => hM i)
    dsimp [A, scale]
    positivity
  have hpoint : ∀ᵐ x ∂haarAddCircle, ‖heat t (iteratedFDeriv ℝ (j+1)
      (globalHaarColumn (some p)) (DyadicApproximation.realEmbed f)
        (fun i => DyadicApproximation.realEmbed (v i))) x‖ ≤
      A * (NodeKernelLocal.constant p t ht x/(((2^(p.length+1):ℕ):ℝ))) := by
    filter_upwards [globalHaarColumn_jet_fine_pointwise hΛ hρ hρhalf ht p hsmall f m U hm hf j v M hM hv] with x hx
    exact hx.trans_eq (by dsimp [A]; ring)
  have hh := GaussianPacketOutput.negative hΛ hρ hρhalf ht ht1 hA p _ hpoint b B hB hb
  have hDs : scale Λ ρ (p.length+1)^2 = (Λ+(((2^(p.length+1):ℕ):ℝ))^2)^ρ := by
    rw [scale, ← Real.rpow_mul_natCast (by positivity : 0 ≤ Λ+(((2^(p.length+1):ℕ):ℝ))^2)]
    congr 1
    norm_num
  exact hh.trans_eq (by dsimp only [A, negativeFineConstant, GaussianPacketOutput.constant]; simp only [mul_pow, hDs]; ring)

end SHE.FiniteHaar
