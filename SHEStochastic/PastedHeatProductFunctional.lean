module

public import SHEStochastic.PastedLinearHeatFunctional
public import SHEStochastic.PastedHeatCovariance

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
noncomputable section

namespace SHEStochastic.PastedHeatProductFunctional
open StoppedPathPasting
open scoped NNReal

variable {E : Type*} [AddCommGroup E] [TopologicalSpace E] [IsTopologicalAddGroup E] [T2Space E]
  [Module ℝ E] (H : ℝ≥0) (ell₁ ell₂ : E →L[ℝ] ℝ) (lam₁ lam₂ : ℝ)
  (hRate : 0 ≤ lam₁+lam₂) (b : BoundedContinuousFunction E ℝ)

local notation "M₁" => PastedLinearHeatFunctional.value H ell₁ lam₁
local notation "M₂" => PastedLinearHeatFunctional.value H ell₂ lam₂
local notation "A" => PastedHeatCovariance.value H (lam₁+lam₂) hRate b

/-- The common compensated product for a square or a mixed driver
characteristic. A driver coordinate is the heat mode with rate zero. -/
def value (x : Path H E) (t : Time H) : ℝ := M₁ x t*M₂ x t-A x t

@[simp] theorem value_origin (x : Path H E) : value H ell₁ ell₂ lam₁ lam₂ hRate b x (origin H) = 0 := by
  simp [value]

theorem continuous_value :
    Continuous (fun p : Path H E × Time H ↦ value H ell₁ ell₂ lam₁ lam₂ hRate b p.1 p.2) :=
  ((PastedLinearHeatFunctional.continuous_value H ell₁ lam₁).mul
    (PastedLinearHeatFunctional.continuous_value H ell₂ lam₂)).sub
      (PastedHeatCovariance.continuous_value H (lam₁+lam₂) hRate b)

theorem usesPast (t : Time H) :
    PastedPastTests.UsesPast H t (fun x ↦ value H ell₁ ell₂ lam₁ lam₂ hRate b x t) := by
  intro x y hxy
  have hL (ell : E →L[ℝ] ℝ) (lam : ℝ) :
      PastedLinearHeatFunctional.value H ell lam x t = PastedLinearHeatFunctional.value H ell lam y t := by
    simp only [PastedLinearHeatFunctional.value, hxy t le_rfl, hxy (origin H) t.property.1]
  exact congrArg₂ (·-·) (congrArg₂ (·*·) (hL ell₁ lam₁) (hL ell₂ lam₂))
    (PathIntegratedCovariance.usesPast H (PathIntegratedCovariance.exponential H (lam₁+lam₂) hRate) b t x y hxy)

/-- The two extra cross terms retain the actual values at the join.
This formula requires no independence of the source prefix. -/
theorem value_paste (r t : Time H) (x y : Path H E) (hjoin : y (origin H) = x r) :
    value H ell₁ ell₂ lam₁ lam₂ hRate b (paste H r x y) t =
      value H ell₁ ell₂ lam₁ lam₂ hRate b x (pastTime H r t)+
      Real.exp ((lam₁+lam₂)*r.val)*value H ell₁ ell₂ lam₁ lam₂ hRate b y (futureTime H r t)+
      (M₁ x r*Real.exp (lam₂*r.val))*M₂ y (futureTime H r t)+
      (M₂ x r*Real.exp (lam₁*r.val))*M₁ y (futureTime H r t) := by
  have he : Real.exp ((lam₁+lam₂)*r.val) = Real.exp (lam₁*r.val)*Real.exp (lam₂*r.val) := by
    rw [add_mul, Real.exp_add]
  unfold value
  rw [PastedLinearHeatFunctional.value_paste H ell₁ lam₁ r t x y hjoin,
    PastedLinearHeatFunctional.value_paste H ell₂ lam₂ r t x y hjoin,
    PastedHeatCovariance.value_paste H (lam₁+lam₂) hRate b r t x y hjoin, he]
  by_cases ht : t.val ≤ r.val
  · have hf : futureTime H r t = origin H := Subtype.ext (max_eq_right (sub_nonpos.mpr ht))
    simp only [hf, PastedLinearHeatFunctional.value_origin, PastedHeatCovariance.value_origin]
    ring
  · rw [show pastTime H r t = r from Subtype.ext (min_eq_right (le_of_not_ge ht))]
    ring

theorem increment_paste (r s t : Time H) (x y : Path H E) (hjoin : y (origin H) = x r) :
    value H ell₁ ell₂ lam₁ lam₂ hRate b (paste H r x y) t-
      value H ell₁ ell₂ lam₁ lam₂ hRate b (paste H r x y) s =
      (value H ell₁ ell₂ lam₁ lam₂ hRate b x (pastTime H r t)-
        value H ell₁ ell₂ lam₁ lam₂ hRate b x (pastTime H r s))+
      Real.exp ((lam₁+lam₂)*r.val)*
        (value H ell₁ ell₂ lam₁ lam₂ hRate b y (futureTime H r t)-
          value H ell₁ ell₂ lam₁ lam₂ hRate b y (futureTime H r s))+
      (M₁ x r*Real.exp (lam₂*r.val))*(M₂ y (futureTime H r t)-M₂ y (futureTime H r s))+
      (M₂ x r*Real.exp (lam₁*r.val))*(M₁ y (futureTime H r t)-M₁ y (futureTime H r s)) := by
  rw [value_paste H ell₁ ell₂ lam₁ lam₂ hRate b r t x y hjoin,
    value_paste H ell₁ ell₂ lam₁ lam₂ hRate b r s x y hjoin]
  ring

theorem test_of_pre_nonzero (s t r : Time H) (hst : s.val ≤ t.val)
    (test : Path H E → ℝ) (htest : PastedPastTests.UsesPast H s test) (x y : Path H E)
    (hne : value H ell₁ ell₂ lam₁ lam₂ hRate b x (pastTime H r t)-
      value H ell₁ ell₂ lam₁ lam₂ hRate b x (pastTime H r s) ≠ 0) :
    test (paste H r x y) = test x := by
  apply PastedPastTests.test_before H s r test htest x y
  apply le_of_not_gt
  intro hrs
  have hs : pastTime H r s = r := Subtype.ext (min_eq_right hrs.le)
  have ht : pastTime H r t = r := Subtype.ext (min_eq_right (hrs.le.trans hst))
  exact hne (by rw [hs, ht, sub_self])

end SHEStochastic.PastedHeatProductFunctional
