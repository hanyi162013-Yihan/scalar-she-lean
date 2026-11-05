module

public import SHE.GradientInputConvergence
public import SHE.StoppedInputContinuity

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
noncomputable section

namespace SHE.FiniteItoNoiseContinuity
open MeasureTheory Filter PredictableL2 FiniteItoNoise StoppedItoInputs
open scoped NNReal ENNReal Topology
variable {Ω C : Type*} [MeasurableSpace Ω]
variable [NormedAddCommGroup C] [InnerProductSpace ℝ C] [CompleteSpace C]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
variable {k : ℕ} (Y : ℝ≥0×Ω→WordRecursion.State k)
variable (hY : StronglyMeasurable[𝓕.predictable] Y) (R : Fin k→Process (E := C) 𝓕 μ H)

theorem tendsto_noise (J : StandardTerminalIto (C := C) (E := ℝ) 𝓕 μ H)
    (a b : ℝ) (G : ℝ→WordRecursion.State k→ℝ) (Gₙ : ℕ→ℝ→WordRecursion.State k→ℝ)
    (hG : AdmissibleGradient G) (hGₙ : ∀ n,AdmissibleGradient (Gₙ n))
    (ht : Tendsto (fun n => gradientProcess 𝓕 μ H Y hY R (Gₙ n) (hGₙ n)) atTop
      (𝓝 (gradientProcess 𝓕 μ H Y hY R G hG))) :
    Tendsto (fun n => noise 𝓕 μ H Y hY R J a b (Gₙ n)) atTop
      (𝓝 (noise 𝓕 μ H Y hY R J a b G)) := by
  have hb := ((StoppedInputAlgebra.stop_continuous (C := C) 𝓕 μ H b).tendsto _).comp ht
  have ha := ((StoppedInputAlgebra.stop_continuous (C := C) 𝓕 μ H a).tendsto _).comp ht
  have hJ := (J.integral.continuous.tendsto _).comp (hb.sub ha)
  have he : (fun n => noise 𝓕 μ H Y hY R J a b (Gₙ n))=
      fun n => J.integral (stop 𝓕 μ H b (gradientProcess 𝓕 μ H Y hY R (Gₙ n) (hGₙ n))-
        stop 𝓕 μ H a (gradientProcess 𝓕 μ H Y hY R (Gₙ n) (hGₙ n))) :=
    funext (fun n => noise_eq 𝓕 μ H Y hY R J a b (Gₙ n) (hGₙ n))
  rw [he,noise_eq 𝓕 μ H Y hY R J a b G hG]
  exact hJ

end SHE.FiniteItoNoiseContinuity
