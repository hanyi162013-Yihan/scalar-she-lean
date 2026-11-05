module

public import SHE.HaarInfinite
public import SHE.DyadicApproximation

@[expose] public section
set_option autoImplicit false

/-! The infinite signed heat estimate for actual uniformly elliptic
measurable coefficients on the circle. Every finite approximation,
coherent input node, and physical column limit is constructed. -/

namespace SHE.FiniteHaar

open MeasureTheory AddCircle CircleHeat
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩

theorem global_signed_heat {t κ Λ ρ : ℝ}
    (ht : 0 < t) (ht1 : t ≤ 1) (hκ : 0 ≤ κ) (hΛ : 0 < Λ)
    (hρ : 0 < ρ) (hρhalf : ρ < 1 / 2)
    (f g : CircleL2) (m U : ℝ) (hm : 0 < m)
    (hfreal : ∀ᵐ y ∂haarAddCircle, (f y).im = 0)
    (hgreal : ∀ᵐ y ∂haarAddCircle, (g y).im = 0)
    (hfbound : ∀ᵐ y ∂haarAddCircle, m ≤ (f y).re ∧ (f y).re ≤ U)
    (hgbound : ∀ᵐ y ∂haarAddCircle, m ≤ (g y).re ∧ (g y).re ≤ U) :
    Summable (fun q : HaarNode => ‖heat t (globalSignedColumn q f g)‖ ^ 2) ∧
      (∑' q : HaarNode, ‖heat t (globalSignedColumn q f g)‖ ^ 2) ≤
        signedHeatSqConstant κ ρ m U * StepInput.negativeEnergy κ Λ ρ (f - g) *
          (Λ ^ ρ * t ^ (-(1 / 2 : ℝ)) + t ^ (-(1 / 2 : ℝ) - ρ)) := by
  exact global_signed_heat_of_grid_approximation ht ht1 hκ hΛ hρ hρhalf
    (fun N => localAverage N f) (fun N => localAverage N g) f g m U hm
    (fun N x => localAverage_bounds_ae N f m U hfbound x)
    (fun N x => localAverage_bounds_ae N g m U hgbound x)
    (DyadicApproximation.average_tendsto_of_real f hfreal)
    (DyadicApproximation.average_tendsto_of_real g hgreal)

theorem global_signed_heat_tail {t κ Λ ρ : ℝ}
    (ht : 1 ≤ t) (hκ : 0 ≤ κ) (hΛ : 0 < Λ)
    (hρ : 0 < ρ) (hρhalf : ρ < 1 / 2)
    (f g : CircleL2) (m U : ℝ) (hm : 0 < m)
    (hfreal : ∀ᵐ y ∂haarAddCircle, (f y).im = 0)
    (hgreal : ∀ᵐ y ∂haarAddCircle, (g y).im = 0)
    (hfbound : ∀ᵐ y ∂haarAddCircle, m ≤ (f y).re ∧ (f y).re ≤ U)
    (hgbound : ∀ᵐ y ∂haarAddCircle, m ≤ (g y).re ∧ (g y).re ≤ U) :
    Summable (fun q : HaarNode => ‖heat t (globalSignedColumn q f g)‖ ^ 2) ∧
      (∑' q : HaarNode, ‖heat t (globalSignedColumn q f g)‖ ^ 2) ≤
        signedHeatSqConstant κ ρ m U * StepInput.negativeEnergy κ Λ ρ (f - g) * (Λ ^ ρ + 1) := by
  exact global_signed_heat_tail_of_grid_approximation ht hκ hΛ hρ hρhalf
    (fun N => localAverage N f) (fun N => localAverage N g) f g m U hm
    (fun N x => localAverage_bounds_ae N f m U hfbound x)
    (fun N x => localAverage_bounds_ae N g m U hgbound x)
    (DyadicApproximation.average_tendsto_of_real f hfreal)
    (DyadicApproximation.average_tendsto_of_real g hgreal)

end SHE.FiniteHaar
