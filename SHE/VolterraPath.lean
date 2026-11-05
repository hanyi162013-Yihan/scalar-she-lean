module

public import SHE.RealHeat
public import SHE.LowBands
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Set

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHE.VolterraPath
open MeasureTheory Set CircleHeat LowBands
open scoped NNReal ENNReal
local instance volterraPath_pFinite : Fact ((2:ENNReal) ≠ ⊤) := ⟨by simp⟩

def unitIntegrand (Λ : ℝ) (U : ℝ≥0 → StateL2) (t : ℝ≥0) (r : ℝ) : StateL2 :=
  Real.exp (-Λ*((t:ℝ)*(1-r))) • RealHeat.realHeat ((t:ℝ)*(1-r)) (U (t*r.toNNReal))

/-- The actual deterministic damped heat convolution of a path. -/
def value (Λ : ℝ) (U : ℝ≥0 → StateL2) (t : ℝ≥0) : StateL2 :=
  ∫ s in (0:ℝ)..(t:ℝ),Real.exp (-Λ*((t:ℝ)-s)) •
    RealHeat.realHeat ((t:ℝ)-s) (U s.toNNReal)

theorem unitIntegrand_continuous (Λ : ℝ) {U : ℝ≥0 → StateL2} (hU : Continuous U) :
    Continuous (fun p : ℝ≥0 × ℝ => unitIntegrand Λ U p.1 p.2) := by
  have ha : Continuous (fun p : ℝ≥0 × ℝ => (p.1:ℝ)*(1-p.2)) := by fun_prop
  have ht : Continuous (fun p : ℝ≥0 × ℝ => p.1*p.2.toNNReal) := by fun_prop
  have hu := hU.comp ht
  have hh := RealHeat.continuous_realHeat_action.comp (ha.prodMk hu)
  change Continuous (fun p : ℝ≥0 × ℝ =>
    RealHeat.realHeat ((p.1:ℝ)*(1-p.2)) (U (p.1*p.2.toNNReal))) at hh
  have he : Continuous (fun p : ℝ≥0 × ℝ => Real.exp (-Λ*((p.1:ℝ)*(1-p.2)))) := by fun_prop
  exact he.smul hh

/-- Exact fixed-domain change of time variable, including t=0. -/
theorem value_eq_unit (Λ : ℝ) (U : ℝ≥0 → StateL2) (t : ℝ≥0) :
    value Λ U t=(t:ℝ) • ∫ r in Icc (0:ℝ) 1,unitIntegrand Λ U t r := by
  let F : ℝ → StateL2 := fun s => Real.exp (-Λ*((t:ℝ)-s)) •
    RealHeat.realHeat ((t:ℝ)-s) (U s.toNNReal)
  have hs := intervalIntegral.smul_integral_comp_mul_left (f := F) (a := (0:ℝ)) (b := 1) (t:ℝ)
  simp only [mul_zero,mul_one] at hs
  change (∫ s in (0:ℝ)..(t:ℝ),F s)=_
  rw [← hs,intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1),← integral_Icc_eq_integral_Ioc]
  congr 1
  apply setIntegral_congr_fun measurableSet_Icc
  intro r hr
  have he : ((t:ℝ)*r).toNNReal=t*r.toNNReal := by
    exact (Real.toNNReal_mul (q := r) t.2).trans
      (congrArg (fun q : ℝ≥0 => q*r.toNNReal) (Real.toNNReal_coe (r := t)))
  have ha : (t:ℝ)-(t:ℝ)*r=(t:ℝ)*(1-r) := by ring
  dsimp only [F,unitIntegrand]
  rw [he,ha]

/-- Continuous paths give continuous deterministic damped heat
convolutions, proved on a fixed compact integration interval. -/
theorem continuous_value (Λ : ℝ) {U : ℝ≥0 → StateL2} (hU : Continuous U) :
    Continuous (value Λ U) := by
  have hi := continuous_parametric_integral_of_continuous
    (μ := (volume:Measure ℝ))
    (f := fun (t : ℝ≥0) (r : ℝ) => unitIntegrand Λ U t r)
    (unitIntegrand_continuous Λ hU) (isCompact_Icc : IsCompact (Icc (0:ℝ) 1))
  have hs : Continuous (fun t : ℝ≥0 => (t:ℝ)) := continuous_subtype_val
  have hc := hs.smul hi
  have he : value Λ U=(fun t : ℝ≥0 => (t:ℝ) • ∫ r in Icc (0:ℝ) 1,unitIntegrand Λ U t r) :=
    funext (value_eq_unit Λ U)
  rw [he]
  exact hc

theorem value_zero (Λ : ℝ) (U : ℝ≥0 → StateL2) : value Λ U 0=0 := by
  rw [value_eq_unit]
  simp

end SHE.VolterraPath
