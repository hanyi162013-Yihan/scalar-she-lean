module

public import SHE.FiniteItoNoise
public import SHE.PastItoAlgebra
public import SHE.StandardTerminalPastCentering

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
noncomputable section

namespace SHE.FiniteItoPastNoise
open Set MeasureTheory PredictableL2 StoppedItoInputs PastItoInputs
open scoped NNReal ENNReal
variable {Ω C : Type*} [MeasurableSpace Ω] [NormedAddCommGroup C] [NormedSpace ℝ C]
  [MeasurableSpace C] [BorelSpace C] [SecondCountableTopology C]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [SFinite μ] (H : ℝ≥0)
variable {n : ℕ} (Y : ℝ≥0×Ω→WordRecursion.State n)
variable (hY : StronglyMeasurable[𝓕.predictable] Y) (R : Fin n→Process (E := C) 𝓕 μ H)
variable (J : StandardTerminalIto (C := C) (E := ℝ) 𝓕 μ H)

/-- The actual gradient Itô term on [v,b] is an original full-H
integral with post-v supported input. -/
theorem noise_eq_post (v b : ℝ≥0) (hvb : v≤b) (G : ℝ→WordRecursion.State n→ℝ)
    (hG : FiniteItoNoise.AdmissibleGradient G) :
    FiniteItoNoise.noise 𝓕 μ H Y hY R J v b G=
      J.integral (post 𝓕 μ H v
        (stop 𝓕 μ H (b:ℝ) (FiniteItoNoise.gradientProcess 𝓕 μ H Y hY R G hG))) := by
  rw [FiniteItoNoise.noise_eq 𝓕 μ H Y hY R J v b G hG,
    PastItoAlgebra.post_stop_eq_sub 𝓕 μ H v b hvb]

/-- Ordinary block1 locality gives the genuine past-event centering
of the martingale term of universal finite-dimensional Itô. -/
theorem noise_centered_on_past_event (hlocal : StandardTerminalPastLocality J)
    (v b : ℝ≥0) (hvb : v≤b) (G : ℝ→WordRecursion.State n→ℝ)
    (A : Set Ω) (hA : MeasurableSet[𝓕 v] A) :
    (∫ ω in A,FiniteItoNoise.noise 𝓕 μ H Y hY R J v b G ω ∂μ)=0 := by
  classical
  by_cases hG : FiniteItoNoise.AdmissibleGradient G
  · rw [noise_eq_post 𝓕 μ H Y hY R J v b hvb G hG]
    exact StandardTerminalPastLocality.centered_on_past_event J hlocal v A hA _
  · rw [FiniteItoNoise.noise,dif_neg hG]
    exact integral_eq_zero_of_ae (ae_restrict_of_ae (Lp.coeFn_zero ℝ 2 μ))

end SHE.FiniteItoPastNoise
