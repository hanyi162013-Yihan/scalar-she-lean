module

public import SHE.IntervalScoreEnvelope
public import SHE.NativeHeatKernel

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHE.IntervalScoreEnvelope
open Set Filter MeasureTheory ProbabilityTheory AddCircle GaussianIncrement StoppedGaussianFeatures
  StoppedFourier OldIntervalCovariance MeasurableGaussianScores
open scoped BigOperators
local instance intervalScoreHeatKernel_periodPositive : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

/-- The manuscript's actual all-order second-score heat envelope. Every
parent is an original active observation, the heat age is twice its true
physical target age, and the prefactor contains exactly the old interval
length. No eigenvalue gap or conditioning constant appears. -/
theorem score_heat_kernel (n : ℕ) :
    ∃ H C : ℝ, 0 < H ∧ 0 < C ∧
      ∀ (σ target : Fin n → ℝ) (center : Fin n → HeatCircle),
      (∀ i, σ i ≤ target i) → ∀ {lo hi ell M : ℝ},
      0 ≤ lo → lo < hi → (∀ i, σ i ≤ lo ∨ hi ≤ σ i) →
      (∀ i, hi ≤ σ i → target i - lo ≤ H) →
      ∀ (c : Domain → ℝ), Measurable c → 0 < ell → (∀ p, ell ≤ c p ∧ c p ≤ M) →
      ∀ᵐ x : HeatCircle ∂haarAddCircle,
        scoreVariance (StoppedGaussianFeatures.stoppedCovariance σ target center (intervalProfile c lo hi) 0)
          (StoppedGaussianFeatures.stoppedRow σ target center (lo,x)) ≤
          (C / (ell * (hi-lo))) *
            ∑ i ∈ IntervalHistoryEnergy.active σ hi,
              ‖ProfileVariance.heatPhysical (2*(target i-lo)) (center i) x‖ := by
  obtain ⟨H,C,hH,hC,henv⟩ := score_envelope n
  refine ⟨H,C*Real.sqrt (8*Real.pi),hH,by positivity,?_⟩
  intro σ target center hages lo hi ell M hlo hgap hstop hsmall c hc hell hb
  have hV := henv σ target center hages hlo hgap hstop hsmall c hc hell hb
  have hW (i : Fin n) (hi' : i ∈ IntervalHistoryEnergy.active σ hi) :=
    NativeHeatSpan.weight_le_physical_ae
      (show 0 < target i-lo by have hs := (Finset.mem_filter.mp hi').2; linarith [hages i]) (center i)
  filter_upwards [hV, (Filter.eventually_all_finset (IntervalHistoryEnergy.active σ hi)).mpr hW] with x hx hw
  have hsum : StoppedHeatSpanEnvelope.weight σ target center lo hi x ≤
      Real.sqrt (8*Real.pi) * ∑ i ∈ IntervalHistoryEnergy.active σ hi,
        ‖ProfileVariance.heatPhysical (2*(target i-lo)) (center i) x‖ := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun i hi' => hw i hi')
  have hh := hx.trans (mul_le_mul_of_nonneg_left hsum
    (div_nonneg hC.le (mul_nonneg hell.le (sub_pos.mpr hgap).le)))
  convert! hh using 1 <;> ring

end SHE.IntervalScoreEnvelope
