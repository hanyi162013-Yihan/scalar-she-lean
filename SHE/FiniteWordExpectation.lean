module

public import SHE.IntegratedPhysicalStep

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
noncomputable section

namespace SHE.FiniteWordExpectation
open Set MeasureTheory Filter Topology IntegratedPhysicalStep
variable {P Ω : Type*} [MeasurableSpace P] [MeasurableSpace Ω] {n : ℕ}

theorem expected_level (D : LevelData P Ω n) (hD : AnalyticConditions D)
    (μ : Measure P) [IsFiniteMeasure μ] (τ : Measure Ω) [IsProbabilityMeasure τ]
    (hIto : ItoConditions D τ) :
    (∫ q : P × Ω,D.leaf q.1 q.2 ∂μ.prod τ)=
      (∫ q : P × Ω,D.reference q.1 q.2 ∂μ.prod τ)+
        ∫ q : P × Ω,D.remainder q.1 q.2 ∂μ.prod τ := by
  obtain ⟨K,hK,hKb⟩ := uniform_level_bound D hD
  have hV : Integrable (fun q : P × Ω => D.leaf q.1 q.2) (μ.prod τ) :=
    (integrable_const K).mono' hD.leaf_measurable.aestronglyMeasurable
      (Eventually.of_forall (fun q => (hKb q.1 q.2).1))
  have hQ : Integrable (fun q : P × Ω => D.reference q.1 q.2) (μ.prod τ) :=
    (integrable_const K).mono' hD.reference_measurable.aestronglyMeasurable
      (Eventually.of_forall (fun q => (hKb q.1 q.2).2.1))
  have hR : Integrable (fun q : P × Ω => D.remainder q.1 q.2) (μ.prod τ) :=
    (integrable_const K).mono' hD.remainder_measurable.aestronglyMeasurable
      (Eventually.of_forall (fun q => (hKb q.1 q.2).2.2.1))
  have hN : Integrable (fun q : P × Ω => D.noiseVersion q.1 q.2) (μ.prod τ) := (hV.sub hQ).sub hR
  have hz (p : P) : (∫ ω,D.noiseVersion p ω ∂τ)=0 := by
    rw [integral_congr_ae (noiseVersion_eq_ito D hD τ hIto p)]
    exact hIto.centered p
  have hzero : (∫ q : P × Ω,D.noiseVersion q.1 q.2 ∂μ.prod τ)=0 := by
    rw [integral_prod _ hN]
    simp only [hz,integral_zero]
  change (∫ q : P × Ω,D.leaf q.1 q.2-D.reference q.1 q.2-D.remainder q.1 q.2 ∂μ.prod τ)=0 at hzero
  have hs₁ := integral_sub (hV.sub hQ) hR
  have hs₂ := integral_sub hV hQ
  simp only [Pi.sub_apply] at hs₁ hs₂
  rw [hs₁,hs₂] at hzero
  linarith only [hzero]

theorem integral_tendsto_of_abs {A I : Type*} [MeasurableSpace A] (ν : Measure A)
    (f : A → ℝ) (F : I → A → ℝ) (l : Filter I)
    (hf : Integrable f ν) (hF : ∀ i,Integrable (F i) ν)
    (ht : Tendsto (fun i => ∫ x,|F i x-f x| ∂ν) l (𝓝 0)) :
    Tendsto (fun i => ∫ x,F i x ∂ν) l (𝓝 (∫ x,f x ∂ν)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  apply squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) ?_ ht
  filter_upwards with i
  rw [← integral_sub (hF i) hf]
  simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm (fun x => F i x-f x)

end SHE.FiniteWordExpectation
