module

public import SHE.FullFutureLaterRow

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
noncomputable section

namespace SHE.FullFutureDampedHeat
open Set Filter MeasureTheory ProbabilityTheory Real AddCircle StoppedFourier StoppedGaussianFeatures
  GaussianIncrement MeasurableGaussianScores WordRecursion StopWeightedRows
open scoped BigOperators
local instance fullFutureWeightedScore_periodPositive : Fact (0<2*π) := ⟨by positivity⟩
variable {n : ℕ}

/-- A uniform physical first-score envelope for the literal stop-weighted
row. The covariance includes the full individually stopped future, with
the SAME stops as the exponential weights. -/
theorem weighted_sqrt_heat_envelope (n : ℕ) :
    ∃ H C : ℝ,0<H ∧ 0<C ∧
      ∀ (Z : Fin n→Observation),(∀ i,(Z i).stop≤(Z i).target) →
      ∀ {q r hi Λ ell M : ℝ},0≤q → q≤r → r<hi → 0≤Λ →
      (∀ i,hi≤(Z i).stop) → (∀ i,(Z i).target-r≤H) →
      ∀ (c : Domain→ℝ),Measurable c → 0<ell → (∀ p,ell≤c p ∧ c p≤M) →
      ∀ᵐ y : HeatCircle ∂haarAddCircle,
        weightedHeatRow Λ Z q r y∈
          (Matrix.toEuclideanCLM (𝕜:=ℝ) (stoppedCovariance
            (fun i=>(Z i).stop) (fun i=>(Z i).target) (fun i=>(Z i).center) c q)).range ∧
        sqrt (scoreVariance (stoppedCovariance
          (fun i=>(Z i).stop) (fun i=>(Z i).target) (fun i=>(Z i).center) c q)
          (weightedHeatRow Λ Z q r y))≤
          sqrt (C/(ell*(hi-r)))*
            ∑ i,sqrt ‖ProfileVariance.heatPhysical (4*((Z i).target-r)) (Z i).center y‖ := by
  obtain ⟨H,C,hH,hC,hV⟩ := later_row_heat_bound n
  refine ⟨H,C,hH,hC,?_⟩
  intro Z hages q r hi Λ ell M hq hqr hrhi hΛ hstop hsmall c hc hell hb
  have he : exp (-Λ*(r-q))≤1 := exp_le_one_iff.mpr (by nlinarith)
  have he2 : exp (-Λ*(r-q))^2≤1 := by nlinarith [exp_pos (-Λ*(r-q))]
  have hδ : 0<hi-r := sub_pos.mpr hrhi
  have hst (i : Fin n) : r+(hi-r)≤(Z i).stop := by linarith [hstop i]
  have hh := hV (fun i=>(Z i).stop) (fun i=>(Z i).target) (fun i=>(Z i).center)
    hages hq hqr hΛ hδ hst hsmall c hc hell hb
  filter_upwards [hh] with y hy
  simp only [←weightedHeatRow_eq] at hy
  refine ⟨hy.1,?_⟩
  have hB : 0≤C/(ell*(hi-r))*
      ∑ i,‖ProfileVariance.heatPhysical (4*((Z i).target-r)) (Z i).center y‖ := by positivity
  have hle := hy.2.trans ((mul_le_mul_of_nonneg_right he2 hB).trans_eq (one_mul _))
  have hs := sqrt_le_sqrt hle
  rw [sqrt_mul (div_nonneg hC.le (mul_nonneg hell.le hδ.le))] at hs
  exact hs.trans (mul_le_mul_of_nonneg_left
    (PhysicalFirstScore.sqrt_sum_le _ (fun _=>norm_nonneg _)) (sqrt_nonneg _))

/-- The true canonical Gaussian first-score moments inherit that same
original-parent envelope. The outer Gaussian is the full q-law, even
though the physical row is evaluated at r. -/
theorem weighted_firstScore_moments (n : ℕ) :
    ∃ H C : ℝ,0<H ∧ 0<C ∧
      ∀ (Z : Fin n→Observation),(∀ i,(Z i).stop≤(Z i).target) →
      ∀ {q r hi Λ ell M : ℝ},0≤q → q≤r → r<hi → 0≤Λ →
      (∀ i,hi≤(Z i).stop) → (∀ i,(Z i).target-r≤H) →
      ∀ (c : Domain→ℝ),Measurable c → 0<ell → (∀ p,ell≤c p ∧ c p≤M) →
      ∀ᵐ y : HeatCircle ∂haarAddCircle,∀ p : ℕ,
        let A := stoppedCovariance (fun i=>(Z i).stop) (fun i=>(Z i).target) (fun i=>(Z i).center) c q
        Integrable (fun z=>|firstScore A (weightedHeatRow Λ Z q r y) z|^(2*p)) (multivariateGaussian 0 A) ∧
          (∫ z,|firstScore A (weightedHeatRow Λ Z q r y) z|^(2*p) ∂multivariateGaussian 0 A)≤
            GaussianAudit.firstScoreMoment p *
              (sqrt (C/(ell*(hi-r)))*
                ∑ i,sqrt ‖ProfileVariance.heatPhysical (4*((Z i).target-r)) (Z i).center y‖)^(2*p) := by
  obtain ⟨H,C,hH,hC,hV⟩ := weighted_sqrt_heat_envelope n
  refine ⟨H,C,hH,hC,?_⟩
  intro Z hages q r hi Λ ell M hq hqr hrhi hΛ hstop hsmall c hc hell hb
  have hA := StoppedCovarianceSplit.covariance_posSemidef
    (fun i=>(Z i).stop) (fun i=>(Z i).target) (fun i=>(Z i).center) hages q hc
    (fun p=>⟨hell.le.trans (hb p).1,(hb p).2⟩)
  filter_upwards [hV Z hages hq hqr hrhi hΛ hstop hsmall c hc hell hb] with y hy
  intro p
  dsimp only
  have hm := firstScore_even_moments hA hy.1 p
  refine ⟨hm.1,?_⟩
  rw [hm.2]
  have hs := pow_le_pow_left₀ (sqrt_nonneg _) hy.2 (2*p)
  rw [pow_mul,Real.sq_sqrt (scoreVariance_nonneg hA hy.1)] at hs
  simpa only [mul_comm] using mul_le_mul_of_nonneg_left hs (GaussianAudit.firstScoreMoment_nonneg p)

end SHE.FullFutureDampedHeat
