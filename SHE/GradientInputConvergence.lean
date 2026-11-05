module

public import SHE.GradientInputDomination
public import SHE.LpCrossDominatedLimit

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
noncomputable section

namespace SHE.GradientInputConvergence
open MeasureTheory Filter PredictableL2 FiniteItoNoise
open scoped NNReal ENNReal Topology
variable {Ω C : Type*} [MeasurableSpace Ω]
variable [NormedAddCommGroup C] [InnerProductSpace ℝ C] [CompleteSpace C]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) (H : ℝ≥0)
variable {k : ℕ} (Y : ℝ≥0×Ω→WordRecursion.State k)
variable (hY : StronglyMeasurable[𝓕.predictable] Y) (R : Fin k→Process (E := C) 𝓕 μ H)

/-- State-localized gradients converge in the genuine predictable L²
input space. A finite row-norm sum supplies the actual integrable
dominator, so no stochastic or moment convergence premise is assumed. -/
theorem tendsto_input (G : ℝ→WordRecursion.State k→ℝ) (Gₙ : ℕ→ℝ→WordRecursion.State k→ℝ)
    (hG : AdmissibleGradient G) (hGₙ : ∀ n,AdmissibleGradient (Gₙ n))
    (L : ℝ) (hL : ∀ t z,‖fderiv ℝ (G t) z‖≤L)
    (hLₙ : ∀ n t z,‖fderiv ℝ (Gₙ n t) z‖≤L)
    (hevent : ∀ t z,∀ᶠ n in atTop,fderiv ℝ (Gₙ n t) z=fderiv ℝ (G t) z) :
    Tendsto (fun n => gradientProcess 𝓕 μ H Y hY R (Gₙ n) (hGₙ n)) atTop
      (𝓝 (gradientProcess 𝓕 μ H Y hY R G hG)) := by
  letI : MeasurableSpace (ℝ≥0×Ω) := 𝓕.predictable
  apply LpCrossDominatedLimit.tendsto (GradientInputDomination.dominator 𝓕 μ H R L)
  · intro n
    exact GradientInputDomination.process_bound 𝓕 μ H Y hY R (hGₙ n) (hLₙ n)
  · exact GradientInputDomination.process_bound 𝓕 μ H Y hY R hG hL
  · have hn : ∀ᵐ p ∂(energyMeasure μ H).trim (predictable_le_product 𝓕),∀ n,
        gradientProcess 𝓕 μ H Y hY R (Gₙ n) (hGₙ n) p=gradientRow 𝓕 μ H Y R (Gₙ n) p :=
      ae_all_iff.mpr (fun n => (gradientRow_memLp 𝓕 μ H Y hY R (hGₙ n)).coeFn_toLp)
    have hg : gradientProcess 𝓕 μ H Y hY R G hG=ᵐ[(energyMeasure μ H).trim (predictable_le_product 𝓕)]
        gradientRow 𝓕 μ H Y R G := (gradientRow_memLp 𝓕 μ H Y hY R hG).coeFn_toLp
    filter_upwards [hn,hg] with p hp hq
    apply tendsto_const_nhds.congr'
    filter_upwards [hevent (p.1:ℝ) (Y p)] with n hder
    rw [hp n,hq]
    simp only [gradientRow,gradientCoefficient,hder]

end SHE.GradientInputConvergence
