module

public import SHE.VolterraPathEnergy
public import SHE.TimeMeasureRestriction

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHE.VolterraProcessEnergy
open MeasureTheory Set PredictableL2 LowBands VolterraPath VolterraPathEnergy
open scoped NNReal ENNReal

theorem causal_energy {Λ : ℝ} (hΛ : 0 ≤ Λ) (U : ℝ≥0 → StateL2)
    (hU : Continuous U) (t : ℝ≥0) :
    ENNReal.ofReal (‖value Λ U t‖^2) ≤
      ENNReal.ofReal (t:ℝ)*(∫⁻ s,ENNReal.ofReal (‖U s‖^2) ∂timeMeasure t) := by
  have hb := value_energy hΛ U hU t
  rw [integral_Icc_eq_integral_Ioc] at hb
  have hcc : IntegrableOn (fun r : ℝ => ‖U r.toNNReal‖^2) (Icc (0:ℝ) (t:ℝ)) :=
    (continuous_memLp_interval (fun r : ℝ => U r.toNNReal) (by fun_prop) t).norm.integrable_sq
  have hioc : IntegrableOn (fun r : ℝ => ‖U r.toNNReal‖^2) (Ioc (0:ℝ) (t:ℝ)) :=
    hcc.mono_set Ioc_subset_Icc_self
  have ho : ENNReal.ofReal (∫ r in Ioc (0:ℝ) (t:ℝ),‖U r.toNNReal‖^2)=
      ∫⁻ s,ENNReal.ofReal (‖U s‖^2) ∂timeMeasure t := by
    rw [timeMeasure_lintegral]
    exact ofReal_integral_eq_lintegral_ofReal hioc (Filter.Eventually.of_forall (fun r => sq_nonneg _))
  have hh := ENNReal.ofReal_le_ofReal hb
  have hmul : ENNReal.ofReal ((t:ℝ)*(∫ r in Ioc (0:ℝ) (t:ℝ),‖U r.toNNReal‖^2)) =
      ENNReal.ofReal (t:ℝ)*ENNReal.ofReal (∫ r in Ioc (0:ℝ) (t:ℝ),‖U r.toNNReal‖^2) :=
    ENNReal.ofReal_mul t.2
  rw [hmul,ho] at hh
  exact hh

variable {Ω : Type*} [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [SFinite μ]
variable (Λ : ℝ) (hΛ : 0 ≤ Λ) (U : ℝ≥0 → Ω → StateL2)
variable (ha : StronglyAdapted 𝓕 U) (hc : ∀ ω,Continuous (fun t => U t ω))

local instance : MeasurableSpace StateL2 := borel StateL2
local instance : BorelSpace StateL2 := ⟨rfl⟩
local instance : Fact ((2:ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩

include hΛ ha hc in
/-- Actual deterministic causal convolution is bounded on time/probability
L² by h², uniformly in nonnegative damping. All measurability and causal
time restrictions are proved for the continuous adapted input. -/
theorem total_energy_bound (h : ℝ≥0) :
    (∫⁻ t,∫⁻ ω,ENNReal.ofReal (‖value Λ (fun s => U s ω) t‖^2) ∂μ ∂timeMeasure h) ≤
      ENNReal.ofReal ((h:ℝ)^2)*(∫⁻ t,∫⁻ ω,ENNReal.ofReal (‖U t ω‖^2) ∂μ ∂timeMeasure h) := by
  have hUPred := ContinuousPredictable.stronglyMeasurable 𝓕 U ha hc
  have hUmeas : Measurable (fun p : ℝ≥0 × Ω => ENNReal.ofReal (‖U p.1 p.2‖^2)) :=
    ENNReal.continuous_ofReal.measurable.comp
      (((hUPred.mono (predictable_le_product 𝓕)).measurable.norm).pow_const 2)
  have hb (t : ℝ≥0) (ht : t ≤ h) (ω : Ω) :
      ENNReal.ofReal (‖value Λ (fun s => U s ω) t‖^2) ≤
        ENNReal.ofReal (h:ℝ)*(∫⁻ s,ENNReal.ofReal (‖U s ω‖^2) ∂timeMeasure h) := by
    apply (causal_energy hΛ (fun s => U s ω) (hc ω) t).trans
    apply mul_le_mul'
    · exact ENNReal.ofReal_le_ofReal (by exact_mod_cast ht)
    · rw [← timeMeasure_restrict ht]
      exact lintegral_mono' Measure.restrict_le_self le_rfl
  calc
    _ ≤ ∫⁻ t,∫⁻ ω,ENNReal.ofReal (h:ℝ)*
        (∫⁻ s,ENNReal.ofReal (‖U s ω‖^2) ∂timeMeasure h) ∂μ ∂timeMeasure h := by
      apply lintegral_mono_ae
      filter_upwards [timeMeasure_ae_mem h] with t ht
      exact lintegral_mono (hb t ht.2)
    _ = ENNReal.ofReal ((h:ℝ)^2)*
        (∫⁻ ω,∫⁻ s,ENNReal.ofReal (‖U s ω‖^2) ∂timeMeasure h ∂μ) := by
      simp only [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,lintegral_const,timeMeasure_mass]
      rw [show ENNReal.ofReal ((h:ℝ)^2)=ENNReal.ofReal (h:ℝ)*ENNReal.ofReal (h:ℝ) by
        calc
          ENNReal.ofReal ((h:ℝ)^2)=ENNReal.ofReal ((h:ℝ)*(h:ℝ)) := congrArg ENNReal.ofReal (pow_two _)
          _ = ENNReal.ofReal (h:ℝ)*ENNReal.ofReal (h:ℝ) := ENNReal.ofReal_mul h.2 ]
      ring
    _ = _ := by
      congr 1
      exact (lintegral_lintegral_swap hUmeas.aemeasurable).symm

end SHE.VolterraProcessEnergy
