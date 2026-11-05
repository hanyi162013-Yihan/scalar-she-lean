module

public import SHEStochastic.PowerTaylorBound
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
noncomputable section

namespace SHEStochastic.PowerMomentAbsorption
open MeasureTheory
open scoped NNReal

/-- A deliberately nonoptimal universal BDG constant. -/
def constant (p : ℕ) : ℝ≥0 :=
  let c : ℝ≥0 := (2*p)*(2*p-1 : ℕ)
  2*c*(8*c)^(p-1)

/-- Absorb the path maximum using Young's inequality and the existing
Doob L² bound for the p-th power. -/
theorem estimate {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (p : ℕ) (hp : 1 ≤ p) (D A : Ω → ℝ)
    (hD : ∀ ω, 0 ≤ D ω) (hA : ∀ ω, 0 ≤ A ω)
    (hDI : Integrable (fun ω ↦ D ω^(2*p)) μ)
    (hAI : Integrable (fun ω ↦ A ω^p) μ)
    (hDAI : Integrable (fun ω ↦ D ω^(2*p-2)*A ω) μ)
    (m : ℝ)
    (hMax : (∫ ω, D ω^(2*p) ∂μ) ≤ 4*m)
    (hFirst : m ≤ ((2*p : ℕ) : ℝ)*(2*p-1 : ℕ)*∫ ω, D ω^(2*p-2)*A ω ∂μ) :
    m ≤ (constant p : ℝ)*∫ ω, A ω^p ∂μ := by
  let c : ℝ := ((2*p : ℕ) : ℝ)*(2*p-1 : ℕ)
  have hc1 : 0 < 2*p := by omega
  have hc2 : 0 < 2*p-1 := by omega
  have hc : 0 < c := mul_pos (Nat.cast_pos.mpr hc1) (Nat.cast_pos.mpr hc2)
  let ε : ℝ := 1/(8*c)
  have hε : 0 < ε := by dsimp only [ε]; positivity
  have hY : (∫ ω, D ω^(2*p-2)*A ω ∂μ) ≤
      ε*(∫ ω, D ω^(2*p) ∂μ)+ε⁻¹^(p-1)*(∫ ω, A ω^p ∂μ) := by
    have hh := integral_mono hDAI ((hDI.const_mul ε).add (hAI.const_mul (ε⁻¹^(p-1))))
      (fun ω ↦ by
        change D ω^(2*p-2)*A ω ≤ ε*D ω^(2*p)+ε⁻¹^(p-1)*A ω^p
        have hy := PowerTaylorBound.young p hp ε hε (D ω^2) (A ω) (sq_nonneg _) (hA ω)
        simpa only [← pow_mul, show 2*(p-1)=2*p-2 by omega] using hy)
    calc
      _ ≤ (∫ ω, ε*D ω^(2*p)+ε⁻¹^(p-1)*A ω^p ∂μ) := hh
      _ = _ := (integral_add (hDI.const_mul ε) (hAI.const_mul (ε⁻¹^(p-1)))).trans
        (congrArg₂ (· + ·) (integral_const_mul _ _) (integral_const_mul _ _))
  have hm : m ≤ c*(ε*(4*m)+ε⁻¹^(p-1)*(∫ ω, A ω^p ∂μ)) :=
    hFirst.trans (mul_le_mul_of_nonneg_left (hY.trans
      (add_le_add (mul_le_mul_of_nonneg_left hMax hε.le) le_rfl)) hc.le)
  have hInv : ε⁻¹=8*c := by simp [ε, one_div]
  have hCancel : c*ε*4 = (1/2 : ℝ) := by
    dsimp only [ε]
    field_simp [ne_of_gt hc]
    <;> ring
  rw [hInv] at hm
  have hExpand : c*(ε*(4*m)+(8*c)^(p-1)*(∫ ω, A ω^p ∂μ)) =
      m/2+c*(8*c)^(p-1)*(∫ ω, A ω^p ∂μ) := by
    calc
      _ = (c*ε*4)*m+c*(8*c)^(p-1)*(∫ ω, A ω^p ∂μ) := by ring
      _ = _ := by rw [hCancel]; ring
  rw [hExpand] at hm
  have hConst : (constant p : ℝ) = 2*c*(8*c)^(p-1) := by
    simp only [constant, NNReal.coe_mul, NNReal.coe_pow, NNReal.coe_ofNat, NNReal.coe_natCast]
    dsimp only [c]
    push_cast
    ring
  rw [hConst]
  nlinarith

end SHEStochastic.PowerMomentAbsorption
