module

public import SHE.FiniteItoBorelRandomFormula

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
namespace SHE.FiniteItoRandomCentering
open Set MeasureTheory PredictableL2 FiniteItoNoise Filter Topology
open scoped NNReal ENNReal
variable {Ω X C : Type*} [MeasurableSpace Ω]
variable [PseudoMetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [NormedAddCommGroup C] [InnerProductSpace ℝ C]
variable [MeasurableSpace C] [BorelSpace C] [SecondCountableTopology C]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
variable {n : ℕ} (Y : ℝ≥0×Ω→WordRecursion.State n)
variable (hY : StronglyMeasurable[𝓕.predictable] Y) (R : Fin n→Process (E:=C) 𝓕 μ H)
variable (G : X→ℝ→WordRecursion.State n→ℝ)
variable (hgm : Measurable (fun p : X×(ℝ×WordRecursion.State n)=>fderiv ℝ (G p.1 p.2.1) p.2.2))
variable (L : ℝ) (hL0 : 0≤L) (hL : ∀ x t z,‖fderiv ℝ (G x t) z‖≤L)
variable (v c : ℝ≥0) (e : X)
variable (J : StandardTerminalIto (C:=C) (E:=ℝ) 𝓕 μ H)
local notation "inp" => FiniteItoBorelGradient.input 𝓕 μ H Y hY R G hgm L hL0 hL v c e

/-- The actual random-test gradient integral is integrable and centered
on EVERY event from its original past sigma algebra. -/
theorem centered (hlocal : StandardTerminalPastLocality J)
    {u : Ω→X} (hu : Measurable[𝓕 v] u) :
    Integrable (J.integral (inp hu)) μ ∧ ∀ A,MeasurableSet[𝓕 v] A→
      (∫ ω in A,J.integral (inp hu) ω ∂μ)=0 := by
  refine ⟨(Lp.memLp _).integrable (by norm_num : (1:ENNReal)≤2),fun A hA=>?_⟩
  have hp : PastItoInputs.post 𝓕 μ H v (inp hu)=inp hu :=
    PastParameterItoIdentity.post_input 𝓕 μ H v
      (FiniteItoGradientFamily.raw 𝓕 μ H Y R G c)
      (FiniteItoBorelGradient.measurable_raw 𝓕 μ H Y hY R G hgm c)
      (FiniteItoGradientMajorant.process 𝓕 μ H R L)
      (FiniteItoGradientFamily.bound 𝓕 μ H Y R G c L hL0 hL) e hu
  rw [←hp]
  exact StandardTerminalPastLocality.centered_on_past_event J hlocal v A hA (inp hu)

end SHE.FiniteItoRandomCentering
