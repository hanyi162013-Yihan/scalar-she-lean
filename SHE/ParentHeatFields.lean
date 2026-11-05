module

public import SHE.ParentHeatIntegration

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
noncomputable section

namespace SHE.OrderedHeatForests
open Set MeasureTheory StoppedFourier NativeHeatAction
open scoped BigOperators
local instance : Fact (0 < 2*Real.pi) := ⟨by positivity⟩
attribute [local irreducible] NativeHeatAction.edge NativeHeatSpan.kernel

theorem parentDensity_continuous {m : ℕ} (κ : ℝ) (hκ : 0 < κ) (k : ℕ)
    (t : Fin (m+k) → ℝ) (ht : OrderedTimes k t) : Continuous (parentDensity κ hκ k t ht) := by
  classical
  have he : parentDensity κ hκ k t ht =
      fun z => ∑ Q : Choices m k, density (ofChoices κ hκ k t ht Q) z :=
    funext (fun z => (sum_density_eq κ hκ k t ht z).symm)
  rw [he]
  exact continuous_finset_sum _ (fun Q _ => density_continuous _)

theorem parentDensity_nonneg {m : ℕ} (κ : ℝ) (hκ : 0 < κ) (k : ℕ)
    (t : Fin (m+k) → ℝ) (ht : OrderedTimes k t) (z : Fin (m+k) → HeatCircle) :
    0 ≤ parentDensity κ hκ k t ht z := by
  rw [← sum_density_eq κ hκ k t ht z]
  exact Finset.sum_nonneg (fun Q _ => density_nonneg _ _)

theorem density_mass {m k : ℕ} (T : Forest m k) (a : Fin m → HeatCircle) :
    (∫ x : Fin k → HeatCircle, density T (values a k x)
      ∂Measure.pi (fun _ : Fin k => AddCircle.haarAddCircle))=1 := by
  have hh := average_eq_integral_continuous T (fun _ => (1 : ℝ)) continuous_const a
  simpa only [mul_one,average_const] using hh.symm

/-- The exact spatial mass of the full earlier-parent envelope is the
number of genuine parent assignments, independent of times and centers. -/
theorem parentDensity_mass {m : ℕ} (κ : ℝ) (hκ : 0 < κ) (k : ℕ)
    (t : Fin (m+k) → ℝ) (ht : OrderedTimes k t) (a : Fin m → HeatCircle) :
    (∫ x : Fin k → HeatCircle, parentDensity κ hκ k t ht (values a k x)
      ∂Measure.pi (fun _ : Fin k => AddCircle.haarAddCircle))=(Fintype.card (Choices m k) : ℝ) := by
  classical
  have hi (Q : Choices m k) : Integrable
      (fun x : Fin k → HeatCircle => density (ofChoices κ hκ k t ht Q) (values a k x))
      (Measure.pi (fun _ : Fin k => AddCircle.haarAddCircle)) :=
    ((density_continuous _).comp (values_continuous a k)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  simp_rw [← sum_density_eq κ hκ k t ht]
  rw [integral_finsetSum _ (fun Q _ => hi Q)]
  simp only [density_mass,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one]

end SHE.OrderedHeatForests
