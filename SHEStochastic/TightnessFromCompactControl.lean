module

public import Mathlib.MeasureTheory.Measure.Tight
public import Mathlib.MeasureTheory.Integral.Lebesgue.Markov

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHEStochastic.TightnessFromCompactControl
open MeasureTheory Set
open scoped ENNReal NNReal

variable {Ω X : Type*} [MeasurableSpace Ω]
  [TopologicalSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X]

/-- A uniform expected control with common compact sublevel sets gives
tightness. This packages Markov's inequality for random Hölder controls;
the control and compact sets must still be supplied explicitly. -/
theorem tight (μ : ℕ → Measure Ω) (Y : ℕ → Ω → X) (hY : ∀ k, Measurable (Y k))
    (C : ℕ → Ω → ℝ≥0∞) (hC : ∀ k, AEMeasurable (C k) (μ k))
    (L : ℝ≥0∞) (hL : L ≠ ⊤) (hbound : ∀ k, (∫⁻ sample, C k sample ∂μ k) ≤ L)
    (hcompact : ∀ R : ℝ≥0, 0 < R → ∃ K : Set X, IsCompact K ∧
      ∀ k, ∀ᵐ sample ∂μ k, C k sample ≤ R → Y k sample ∈ K) :
    IsTightMeasureSet (Set.range (fun k ↦ (μ k).map (Y k))) := by
  apply isTightMeasureSet_iff_exists_isCompact_measure_compl_le.mpr
  intro ε hε
  by_cases hεtop : ε = ⊤
  · subst ε
    exact ⟨∅, isCompact_empty, fun _ _ ↦ le_top⟩
  have hε0 : ε ≠ 0 := ne_of_gt hε
  have hdiv : L / ε ≠ ⊤ := ENNReal.div_ne_top hL hε0
  let R : ℝ≥0 := (L / ε).toNNReal + 1
  have hR : 0 < R := by dsimp [R]; positivity
  have hR0 : (R : ℝ≥0∞) ≠ 0 := by exact_mod_cast hR.ne'
  have hRtop : (R : ℝ≥0∞) ≠ ⊤ := ENNReal.coe_ne_top
  have hchoose : L / ε ≤ (R : ℝ≥0∞) := by
    rw [← ENNReal.coe_toNNReal hdiv]
    exact_mod_cast (le_add_of_nonneg_right (show (0 : ℝ≥0) ≤ 1 by norm_num))
  have hratio : L / R ≤ ε := by
    apply (ENNReal.div_le_iff hR0 hRtop).mpr
    calc
      L = (L / ε) * ε := (ENNReal.div_mul_cancel hε0 hεtop).symm
      _ ≤ (R : ℝ≥0∞) * ε := mul_le_mul' hchoose le_rfl
      _ = ε * R := mul_comm _ _
  obtain ⟨K, hK, hsub⟩ := hcompact R hR
  refine ⟨K, hK, ?_⟩
  rintro _ ⟨k, rfl⟩
  rw [Measure.map_apply (hY k) hK.measurableSet.compl]
  calc
    _ ≤ μ k {sample | (R : ℝ≥0∞) ≤ C k sample} := by
      apply measure_mono_ae
      filter_upwards [hsub k] with sample hs hbad
      exact (lt_of_not_ge (fun h ↦ hbad (hs h))).le
    _ ≤ (∫⁻ sample, C k sample ∂μ k) / R :=
      meas_ge_le_lintegral_div (hC k) hR0 hRtop
    _ ≤ L / R := ENNReal.div_le_div_right (hbound k) _
    _ ≤ ε := hratio

/-- Tight marginals give tight joint laws, allowing arbitrary dependence
and a different coupling at every approximation index. -/
theorem paired {Y : Type*} [TopologicalSpace Y] [MeasurableSpace Y]
    (μ : Measure Ω) (f : ℕ → Ω → X) (g : ℕ → Ω → Y)
    (hf : ∀ k, Measurable (f k)) (hg : ∀ k, Measurable (g k))
    (htf : IsTightMeasureSet (Set.range (fun k ↦ μ.map (f k))))
    (htg : IsTightMeasureSet (Set.range (fun k ↦ μ.map (g k)))) :
    IsTightMeasureSet (Set.range (fun k ↦ μ.map (fun sample ↦ (f k sample, g k sample)))) := by
  let Q (k : ℕ) := μ.map (fun sample ↦ (f k sample, g k sample))
  have he₁ : Measure.fst '' Set.range Q = Set.range (fun k ↦ μ.map (f k)) := by
    rw [← Set.range_comp']
    congr 1
    funext k
    exact Measure.fst_map_prodMk (hf k) (hg k)
  have he₂ : Measure.snd '' Set.range Q = Set.range (fun k ↦ μ.map (g k)) := by
    rw [← Set.range_comp']
    congr 1
    funext k
    exact Measure.snd_map_prodMk (hf k) (hg k)
  exact IsTightMeasureSet.prodMk (by rwa [he₁]) (by rwa [he₂])

end SHEStochastic.TightnessFromCompactControl
