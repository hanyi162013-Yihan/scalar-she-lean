module

public import SHE.FiniteItoNoise

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
noncomputable section

namespace SHE.GradientInputDomination
open MeasureTheory FiniteItoNoise PredictableL2
open scoped NNReal ENNReal
variable {Ω C : Type*} [MeasurableSpace Ω] [NormedAddCommGroup C] [NormedSpace ℝ C]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) (H : ℝ≥0)
variable {k : ℕ} (Y : ℝ≥0×Ω→WordRecursion.State k)
variable (hY : StronglyMeasurable[𝓕.predictable] Y)
variable (R : Fin k→Process (E := C) 𝓕 μ H)

theorem row_bound {G : ℝ→WordRecursion.State k→ℝ} {L : ℝ}
    (hL : ∀ t z,‖fderiv ℝ (G t) z‖≤L) (p : ℝ≥0×Ω) :
    ‖gradientRow 𝓕 μ H Y R G p‖≤L*∑ i : Fin k,‖R i p‖ := by
  calc
    _≤∑ i : Fin k,‖gradientCoefficient Y G i p • R i p‖ := norm_sum_le _ _
    _≤∑ i : Fin k,L*‖R i p‖ := by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_smul]
      exact mul_le_mul_of_nonneg_right (gradientCoefficient_bound Y hL i p) (norm_nonneg _)
    _=_ := (Finset.mul_sum _ _ _).symm

theorem dominator_memLp (L : ℝ) :
    @MemLp _ _ 𝓕.predictable _ _ (fun p => L*∑ i : Fin k,‖R i p‖) 2
      ((energyMeasure μ H).trim (predictable_le_product 𝓕)) := by
  have hs : @MemLp _ _ 𝓕.predictable _ _ (fun p => ∑ i : Fin k,‖R i p‖) 2
      ((energyMeasure μ H).trim (predictable_le_product 𝓕)) := by
    apply memLp_finsetSum
    intro i _
    exact (Lp.memLp (R i)).norm
  have hh := hs.const_smul L
  have he : (L • (fun p : ℝ≥0×Ω => ∑ i : Fin k,‖R i p‖))=
      fun p => L*∑ i : Fin k,‖R i p‖ := by funext p; rfl
  rw [he] at hh
  exact hh

def dominator (L : ℝ) : Process (E := ℝ) 𝓕 μ H :=
  (dominator_memLp 𝓕 μ H R L).toLp (fun p => L*∑ i : Fin k,‖R i p‖)

include hY in
theorem process_bound {G : ℝ→WordRecursion.State k→ℝ} (hG : AdmissibleGradient G) {L : ℝ}
    (hL : ∀ t z,‖fderiv ℝ (G t) z‖≤L) :
    ∀ᵐ p ∂(energyMeasure μ H).trim (predictable_le_product 𝓕),
      ‖gradientProcess 𝓕 μ H Y hY R G hG p‖≤‖dominator 𝓕 μ H R L p‖ := by
  have hg : gradientProcess 𝓕 μ H Y hY R G hG=ᵐ[(energyMeasure μ H).trim (predictable_le_product 𝓕)]
      gradientRow 𝓕 μ H Y R G := (gradientRow_memLp 𝓕 μ H Y hY R hG).coeFn_toLp
  have hd : dominator 𝓕 μ H R L=ᵐ[(energyMeasure μ H).trim (predictable_le_product 𝓕)]
      fun p => L*∑ i : Fin k,‖R i p‖ := (dominator_memLp 𝓕 μ H R L).coeFn_toLp
  filter_upwards [hg,hd] with p hp hq
  rw [hp,hq,Real.norm_eq_abs]
  exact (row_bound 𝓕 μ H Y R hL p).trans (le_abs_self _)

end SHE.GradientInputDomination
