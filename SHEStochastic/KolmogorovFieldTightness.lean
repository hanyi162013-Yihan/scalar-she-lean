module

public import SHEStochastic.KolmogorovFieldControl
public import SHEStochastic.TightnessFromCompactControl

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 700000
noncomputable section

namespace SHEStochastic.KolmogorovFieldTightness
open MeasureTheory ProbabilityTheory Set Metric KolmogorovFieldControl
open scoped ENNReal NNReal

variable {Ω T V : Type*} [MeasurableSpace Ω]
  [MetricSpace T] [CompactSpace T] [SecondCountableTopology T]
  [NormedAddCommGroup V] [ProperSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]

/-- Quantitative Chentsov plus Arzela-Ascoli gives uniform tightness of
continuous field laws. All constants are common to the family; a single
zero anchor suffices. There is no assumed compactness of solution laws. -/
theorem tight (μ : ℕ → Measure Ω) (Y : ℕ → Ω → C(T, V))
    (hY : ∀ k, Measurable (Y k)) (t₀ : T)
    (hzero : ∀ k, ∀ᵐ sample ∂μ k, Y k sample t₀ = 0)
    {c : ℝ≥0∞} {d p q : ℝ} {M : ℝ≥0} {α : ℝ≥0}
    (hT : HasCoveringExponent (Set.univ : Set T) c d)
    (hc : c ≠ ⊤) (hd : 0 < d) (hp : 0 < p) (hdq : d < q)
    (hα : 0 < α) (hαpq : (α : ℝ) < (q - d) / p)
    (hX : ∀ k, IsKolmogorovProcess (fun t sample ↦ Y k sample t) (μ k) p q M) :
    IsTightMeasureSet (Set.range (fun k ↦ (μ k).map (Y k))) := by
  obtain ⟨D, hDcount, hDdense⟩ := TopologicalSpace.exists_countable_dense T
  letI : Countable D := hDcount
  letI : Countable (D ∩ Set.univ : Set T) := hDcount.mono inter_subset_left
  let C (k : ℕ) (sample : Ω) := control D p α (Y k sample)
  let L : ℝ≥0∞ := (M : ℝ≥0∞) * constL c d p q α
  apply TightnessFromCompactControl.tight μ Y hY C
    (fun k ↦ ((measurable_control D p α hDcount).comp (hY k)).aemeasurable) L
  · exact (ENNReal.mul_lt_top ENNReal.coe_lt_top
      (constL_lt_top hc hd hp hdq hαpq)).ne
  · intro k
    exact countable_kolmogorov_chentsov hT (hX k).IsAEKolmogorovProcess hd hdq
      (by exact_mod_cast hα) (D ∩ Set.univ) (subset_univ _)
  · intro R _hR
    let K : ℝ≥0 := ((R : ℝ≥0∞) ^ p⁻¹).toNNReal
    let e := ContinuousMap.isometryEquivBoundedOfCompact T V
    refine ⟨e.symm '' HolderCompactFamily.anchoredSet t₀ 0 K α,
      (HolderCompactFamily.isCompact_anchoredSet t₀ 0 K α K.property
        (by exact_mod_cast hα)).image e.symm.continuous, ?_⟩
    intro k
    filter_upwards [hzero k] with sample hz hbound
    refine ⟨e (Y k sample), ⟨?_, ?_⟩, e.symm_apply_apply _⟩
    · change ‖Y k sample t₀‖ ≤ 0
      rw [hz, norm_zero]
    · intro s t
      exact distance_bound_of_le D p α hDdense hT hp hα (Y k sample) R hbound s t

end SHEStochastic.KolmogorovFieldTightness
