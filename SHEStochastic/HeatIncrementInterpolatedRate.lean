module

public import SHEStochastic.NormalizedHolderEnergy
public import SHEStochastic.HeatIncrementRateAlgebra

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHEStochastic.HeatIncrementInterpolatedRate
open MeasureTheory
open scoped NNReal ENNReal

/-- Coefficient-weighted heat increment interpolation on any finite
time range. Normalization of the spatial measure removes both former
restrictions t≤1 and δ≤1. -/
theorem bound {X E V : Type*} [MeasurableSpace X] [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] [NormedAddCommGroup V]
    {ν : Measure X} [IsProbabilityMeasure ν] {G : E → V} {C β : ℝ≥0}
    (hG : HolderWith C β G) (hβ1 : β≤1) (u : Lp E 2 ν)
    (h : X → ℝ≥0∞) (hh : AEMeasurable h ν)
    {K t δ : ℝ} (hK : 0<K) (ht : 0<t) (hδ : 0≤δ)
    (hcap : ∀ᵐ x ∂ν, h x≤ENNReal.ofReal (4*(K*t^(-(1/2:ℝ)))^2))
    (henergy : (∫⁻ x, h x ∂ν)≤ENNReal.ofReal (K*δ^(1/4:ℝ)*t^(-(3/4:ℝ)))) :
    (∫⁻ x, h x*ENNReal.ofReal (‖G (u x)‖^2) ∂ν)≤
      ENNReal.ofReal (2*(‖G 0‖+(C:ℝ))^2*4^(β:ℝ)*K^(1+(β:ℝ))*
        δ^((1-(β:ℝ))/4)*t^(-(3+(β:ℝ))/4))*(1+ENNReal.ofReal (‖u‖^2)^(β:ℝ)) := by
  let L : ℝ := 4*(K*t^(-(1/2:ℝ)))^2
  let Q : ℝ := K*δ^(1/4:ℝ)*t^(-(3/4:ℝ))
  let B : ℝ := 4^(β:ℝ)*K^(1+(β:ℝ))*δ^((1-(β:ℝ))/4)*t^(-(3+(β:ℝ))/4)
  have hL : 0≤L := by dsimp [L]; positivity
  have hQ : 0≤Q := by dsimp [Q]; positivity
  have hβ : (β:ℝ)≤1 := by exact_mod_cast hβ1
  have hFactor : ENNReal.ofReal L^(β:ℝ)*ENNReal.ofReal Q^(1-(β:ℝ))=ENNReal.ofReal B := by
    calc
      _ = ENNReal.ofReal (L^(β:ℝ))*ENNReal.ofReal (Q^(1-(β:ℝ))) :=
        congrArg₂ (·*·) (ENNReal.ofReal_rpow_of_nonneg hL β.property)
          (ENNReal.ofReal_rpow_of_nonneg hQ (sub_nonneg.mpr hβ))
      _ = ENNReal.ofReal (L^(β:ℝ)*Q^(1-(β:ℝ))) :=
        (ENNReal.ofReal_mul (Real.rpow_nonneg hL (β:ℝ))).symm
      _ = _ := congrArg ENNReal.ofReal (HeatIncrementRateAlgebra.factorization hK ht hδ)

  have hw := NormalizedHolderEnergy.bound hG hβ1 u h hh (ENNReal.ofReal L) (ENNReal.ofReal Q) hcap henergy
  rw [hFactor, ← ENNReal.ofReal_mul (by positivity : 0≤2*(‖G 0‖+(C:ℝ))^2)] at hw
  convert! hw using 1
  congr 2
  dsimp [B]
  ring

end SHEStochastic.HeatIncrementInterpolatedRate
