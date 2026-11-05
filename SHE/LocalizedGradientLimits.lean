module

public import SHE.LocalizedItoTest
public import SHE.FiniteItoNoiseContinuity

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
noncomputable section

namespace SHE.LocalizedGradientLimits
open MeasureTheory Filter PredictableL2 FiniteItoNoise LocalizedItoTest UniformSmooth
open scoped NNReal ENNReal Topology

theorem admissible {k : ℕ} (G : ℝ→WordRecursion.State k→ℝ)
    (hc : Continuous (fun p : ℝ×WordRecursion.State k => G p.1 p.2))
    (hs : UniformBoundedSmooth G) : AdmissibleGradient G := by
  obtain ⟨B,hB,hDb⟩ := hs.fderiv.fderiv.norm_bound
  obtain ⟨L,_,hL⟩ := hs.fderiv.norm_bound
  exact ⟨ParameterSmoothContinuity.continuous_fderiv G hc
    (fun t => (hs.smooth t).of_le (by simp)) hB hDb,L,hL⟩

theorem localized_admissible {k : ℕ} (G : ℝ→WordRecursion.State k→ℝ)
    (hc : Continuous (fun p : ℝ×WordRecursion.State k => G p.1 p.2))
    (hs : UniformBoundedSmooth G) (n : ℕ) : AdmissibleGradient (localized n G) :=
  admissible (localized n G)
    (((StateCutoff.smooth ((n:ℝ)+1)).continuous.comp continuous_snd).mul hc) (fixed_uniform hs n)

variable {Ω C : Type*} [MeasurableSpace Ω]
variable [NormedAddCommGroup C] [InnerProductSpace ℝ C] [CompleteSpace C]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) (H : ℝ≥0)
variable {k : ℕ} (Y : ℝ≥0×Ω→WordRecursion.State k)
variable (hY : StronglyMeasurable[𝓕.predictable] Y) (R : Fin k→Process (E := C) 𝓕 μ H)

theorem input_tendsto (G : ℝ→WordRecursion.State k→ℝ)
    (hc : Continuous (fun p : ℝ×WordRecursion.State k => G p.1 p.2)) (hs : UniformBoundedSmooth G) :
    Tendsto (fun n => gradientProcess 𝓕 μ H Y hY R (localized n G) (localized_admissible G hc hs n)) atTop
      (𝓝 (gradientProcess 𝓕 μ H Y hY R G (admissible G hc hs))) := by
  obtain ⟨L,_,hL⟩ := (uniform_localized hs).fderiv.norm_bound
  obtain ⟨M,_,hM⟩ := hs.fderiv.norm_bound
  apply GradientInputConvergence.tendsto_input 𝓕 μ H Y hY R G (fun n => localized n G)
    (admissible G hc hs) (localized_admissible G hc hs) (max L M)
    (fun t z => (hM t z).trans (le_max_right L M))
    (fun n t z => (hL (n,t) z).trans (le_max_left L M))
  intro t z
  have he := (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n:ℝ)) atTop atTop).eventually
    (eventually_gt_atTop ‖z‖)
  filter_upwards [he] with n hn
  exact (localized_jets_eq n G t (by linarith : ‖z‖<(n:ℝ)+1)).2.1

theorem noise_tendsto [IsProbabilityMeasure μ]
    (J : StandardTerminalIto (C := C) (E := ℝ) 𝓕 μ H) (a b : ℝ)
    (G : ℝ→WordRecursion.State k→ℝ)
    (hc : Continuous (fun p : ℝ×WordRecursion.State k => G p.1 p.2)) (hs : UniformBoundedSmooth G) :
    Tendsto (fun n => noise 𝓕 μ H Y hY R J a b (localized n G)) atTop
      (𝓝 (noise 𝓕 μ H Y hY R J a b G)) :=
  FiniteItoNoiseContinuity.tendsto_noise 𝓕 μ H Y hY R J a b G (fun n => localized n G)
    (admissible G hc hs) (localized_admissible G hc hs) (input_tendsto 𝓕 μ H Y hY R G hc hs)

end SHE.LocalizedGradientLimits
