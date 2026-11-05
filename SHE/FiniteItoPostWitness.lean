module

public import SHE.FiniteItoPastNoise
public import SHE.PastItoAlgebra

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
namespace SHE.FiniteItoPostWitness
open Set MeasureTheory PredictableL2 PastItoInputs
open scoped NNReal ENNReal
variable {Ω C:Type*} [MeasurableSpace Ω] [NormedAddCommGroup C] [NormedSpace ℝ C]
variable [MeasurableSpace C] [BorelSpace C] [SecondCountableTopology C]
variable (𝓕:Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ:Measure Ω) [SFinite μ] (H:ℝ≥0)
variable {n:ℕ} (Y:ℝ≥0×Ω→WordRecursion.State n)
variable (hY:StronglyMeasurable[𝓕.predictable] Y) (R:Fin n→Process (E:=C) 𝓕 μ H)
variable (J:StandardTerminalIto (C:=C) (E:=ℝ) 𝓕 μ H)

/-- Every named finite-Ito noise has an actual original predictable
input supported after its original left endpoint, including the total
definition's zero branch. -/
theorem original_post_input (v b:ℝ≥0) (hvb:v≤b) (G:ℝ→WordRecursion.State n→ℝ):
    ∃input:Process (E:=C) 𝓕 μ H,J.integral (post 𝓕 μ H v input)=
      FiniteItoNoise.noise 𝓕 μ H Y hY R J v b G:=by
  classical
  by_cases hG:FiniteItoNoise.AdmissibleGradient G
  · exact ⟨StoppedItoInputs.stop 𝓕 μ H b (FiniteItoNoise.gradientProcess 𝓕 μ H Y hY R G hG),
      (FiniteItoPastNoise.noise_eq_post 𝓕 μ H Y hY R J v b hvb G hG).symm⟩
  · refine ⟨0,?_⟩
    have hz:post 𝓕 μ H v (0:Process (E:=C) 𝓕 μ H)=0:=by
      apply PastItoAlgebra.eq_of_ambient_ae
      filter_upwards [post_ae 𝓕 μ H v (0:Process (E:=C) 𝓕 μ H),
        ae_eq_of_ae_eq_trim (Lp.coeFn_zero C 2 ((energyMeasure μ H).trim (predictable_le_product 𝓕)))] with z hz h0
      rw [hz,h0]
      split_ifs <;> rfl
    rw [hz,map_zero,FiniteItoNoise.noise,dite_eq_right hG]

end SHE.FiniteItoPostWitness
