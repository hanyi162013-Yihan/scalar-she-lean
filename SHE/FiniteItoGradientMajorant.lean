module

public import SHE.FiniteItoNoise
public import SHE.PastParameterItoInput

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
namespace SHE.FiniteItoGradientMajorant
open Set MeasureTheory PredictableL2 FiniteItoNoise
open scoped NNReal ENNReal
variable {Ω C : Type*} [MeasurableSpace Ω] [NormedAddCommGroup C] [InnerProductSpace ℝ C]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) (H : ℝ≥0)
variable {n : ℕ} (R : Fin n→Process (E:=C) 𝓕 μ H) (L : ℝ)

def raw (p : ℝ≥0×Ω) : ℝ := L*∑ i,‖R i p‖

theorem raw_memLp : @MemLp (ℝ≥0×Ω) ℝ 𝓕.predictable _ _ (raw 𝓕 μ H R L) 2
    ((energyMeasure μ H).trim (predictable_le_product 𝓕)) := by
  exact (memLp_finsetSum _ (fun i _=>(Lp.memLp (R i)).norm)).const_mul L

def process : Process (E:=ℝ) 𝓕 μ H := (raw_memLp 𝓕 μ H R L).toLp (raw 𝓕 μ H R L)

theorem process_ae : process 𝓕 μ H R L =ᵐ[(energyMeasure μ H).trim (predictable_le_product 𝓕)] raw 𝓕 μ H R L :=
  (raw_memLp 𝓕 μ H R L).coeFn_toLp

theorem row_bound (Y : ℝ≥0×Ω→WordRecursion.State n) (G : ℝ→WordRecursion.State n→ℝ)
    (hL : ∀ t z,‖fderiv ℝ (G t) z‖≤L) (p : ℝ≥0×Ω) :
    ‖gradientRow 𝓕 μ H Y R G p‖≤raw 𝓕 μ H R L p := by
  calc
    _ ≤ ∑ i,‖gradientCoefficient Y G i p • R i p‖ := norm_sum_le _ _
    _ ≤ ∑ i,L*‖R i p‖ := Finset.sum_le_sum (fun i _=>by
      rw [norm_smul]
      exact mul_le_mul_of_nonneg_right (gradientCoefficient_bound Y hL i p) (norm_nonneg _))
    _ = _ := by simp only [raw,Finset.mul_sum]

/-- A single actual predictable L² majorant controls ALL bounded-gradient
family parameters on ONE event. This permits later random past selection. -/
theorem family_bound {X : Type*} (Y : ℝ≥0×Ω→WordRecursion.State n)
    (G : X→ℝ→WordRecursion.State n→ℝ) (hL0 : 0≤L)
    (hL : ∀ x t z,‖fderiv ℝ (G x t) z‖≤L) :
    ∀ᵐ p ∂(energyMeasure μ H).trim (predictable_le_product 𝓕),∀ x,
      ‖gradientRow 𝓕 μ H Y R (G x) p‖≤‖process 𝓕 μ H R L p‖ := by
  filter_upwards [process_ae 𝓕 μ H R L] with p hp x
  rw [hp,Real.norm_eq_abs]
  exact (row_bound 𝓕 μ H R L Y (G x) (hL x) p).trans (le_abs_self _)

end SHE.FiniteItoGradientMajorant
