module

public import SHEStochastic.ScalarStoppedMildMoment
public import SHEStochastic.ScalarPredictableNormStop

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section

namespace SHEStochastic.ScalarStoppedMomentProfiles
open MeasureTheory Set SHE SHE.PredictableL2 SHE.DyadicApproximation
open ScalarStoppedMildMoment
open scoped NNReal ENNReal

local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by simp⟩

variable {Ω : Type*} [MeasurableSpace Ω]
  (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›)
  (μ : Measure Ω) [IsProbabilityMeasure μ]
  (W : ℝ≥0 → Ω → RealL2) (hW : StronglyMeasurable[F.predictable] (Function.uncurry W))
  (hc : ∀ ω,Continuous (fun t => W t ω)) (N : ℕ)

local notation "τ" => ContinuousNormExit.exit W N

def second (t : ℝ≥0) : ℝ≥0∞ := ∫⁻ ω,ENNReal.ofReal (liveNormSq W N t ω) ∂μ

def growth (t : ℝ≥0) : ℝ≥0∞ := ∫⁻ ω,ENNReal.ofReal (liveGrowth W N t ω) ∂μ

include hW hc in
theorem norm_measurable : Measurable (fun p : ℝ≥0×Ω => liveNormSq W N p.1 p.2) := by
  classical
  exact Measurable.ite
    (predictable_le_product F _ (ScalarPredictableNormStop.predictable F W hW hc N))
    ((hW.mono (predictable_le_product F)).norm.pow 2).measurable measurable_const

include hW hc in
theorem growth_measurable : Measurable (fun p : ℝ≥0×Ω => liveGrowth W N p.1 p.2) := by
  classical
  exact Measurable.ite
    (predictable_le_product F _ (ScalarPredictableNormStop.predictable F W hW hc N))
    (((hW.mono (predictable_le_product F)).norm.pow 2).measurable.const_add 1) measurable_const

include hW hc in
theorem second_measurable : Measurable (second μ W N) :=
  (norm_measurable F W hW hc N).ennreal_ofReal.lintegral_prod_right'

include hW hc in
theorem profile_measurable : Measurable (growth μ W N) :=
  (growth_measurable F W hW hc N).ennreal_ofReal.lintegral_prod_right'

include hc in
theorem second_le (t : ℝ≥0) : second μ W N t≤((N : ℝ≥0)^2 : ℝ≥0∞) := by
  have ht (ω : Ω) : ENNReal.ofReal (liveNormSq W N t ω) ≤ ((N : ℝ≥0)^2 : ℝ≥0∞) := by
    by_cases h : (t : WithTop ℝ≥0) < τ ω
    · rw [liveNormSq,ite_eq_left h]
      have hN : ((N : ℝ≥0)^2 : ℝ≥0∞) = ENNReal.ofReal ((N : ℝ)^2) := by
        rw [←NNReal.coe_natCast,←NNReal.coe_pow,ENNReal.ofReal_coe_nnreal]
        rw [ENNReal.coe_pow]
      rw [hN]
      exact ENNReal.ofReal_le_ofReal
        (pow_le_pow_left₀ (norm_nonneg _) (ContinuousNormExit.before_bound W hc N t ω h).le 2)
    · rw [liveNormSq,ite_eq_right h,ENNReal.ofReal_zero]
      exact zero_le
  exact (lintegral_mono ht).trans_eq (by rw [lintegral_const,measure_univ,mul_one])

theorem growth_le (t : ℝ≥0) : growth μ W N t≤1+second μ W N t := by
  have h (ω : Ω) : ENNReal.ofReal (liveGrowth W N t ω)≤1+ENNReal.ofReal (liveNormSq W N t ω) := by
    by_cases h : (t : WithTop ℝ≥0) < τ ω
    · rw [liveGrowth,liveNormSq,ite_eq_left h,ite_eq_left h,
        ENNReal.ofReal_add zero_le_one (sq_nonneg _),ENNReal.ofReal_one]
    · rw [liveGrowth,ite_eq_right h,ENNReal.ofReal_zero]
      exact zero_le
  exact (lintegral_mono h).trans_eq (by
    rw [lintegral_add_left measurable_const,lintegral_const,measure_univ,mul_one]
    rfl)

/-- The full state moment is the increasing limit of the physical
pre-exit moments. All positive deterministic horizons are exhausted. -/
theorem full_eq_iSup (t : ℝ≥0) (ω : Ω) (hc : ∀ ω,Continuous (fun t => W t ω)) :
    ENNReal.ofReal (‖W t ω‖^2)=⨆ N : ℕ,ENNReal.ofReal (liveNormSq W N t ω) := by
  apply le_antisymm
  · have h := ContinuousNormExit.tendsto_top W hc ω
    rw [WithTop.tendsto_nhds_top_iff] at h
    obtain ⟨N,hN⟩ := (h t).exists
    exact (le_iSup (fun N => ENNReal.ofReal (liveNormSq W N t ω)) N).trans_eq' (by rw [liveNormSq,ite_eq_left hN])
  · apply iSup_le
    intro N
    by_cases h : (t : WithTop ℝ≥0)<ContinuousNormExit.exit W N ω
    · rw [liveNormSq,ite_eq_left h]
    · rw [liveNormSq,ite_eq_right h,ENNReal.ofReal_zero]
      exact zero_le

end SHEStochastic.ScalarStoppedMomentProfiles
