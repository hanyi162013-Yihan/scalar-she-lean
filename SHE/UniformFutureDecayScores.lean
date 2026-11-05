module

public import SHE.UniformFutureProfileScores

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section

namespace SHE.UniformFutureProfileScores
open Set Filter MeasureTheory AddCircle Real StoppedFourier StoppedGaussianFeatures
  GaussianIncrement MeasurableGaussianScores WordRecursion StopWeightedRows FullFutureScoreOrder
open scoped BigOperators
local instance uniformFutureDecayScores_periodPositive : Fact (0<2*π) := ⟨by positivity⟩
variable {ι : Type*} {n : ℕ}

/-- Exact exponential row factorization, with original stop damping
anchored at q and the physical heat direction at the genuinely later r. -/
theorem weighted_row_factor (Λ : ℝ) (Z : Fin n→Observation) (q r : ℝ) (y : HeatCircle) :
    weightedHeatRow Λ Z q r y=exp (-Λ*(r-q)) • weightedHeatRow Λ Z r r y := by
  simp only [FullFutureDampedHeat.weightedHeatRow_eq]
  exact FullFutureDampedHeat.row_factor _ _ _ q Λ r y

/-- The common all-profile event retains the TRUE exponential decay.
The actual Gaussian law stays at q; covariance order transfers the r-law
range and energy before applying the exact row factorization. -/
theorem weighted_decay_all_profiles_ae (Z : Fin n→Observation)
    (hages : ∀ i,(Z i).stop ≤ (Z i).target) {q r hi Λ ell M : ℝ}
    (hq : 0 ≤ q) (hqr : q ≤ r) (hrhi : r<hi) (hΛ : 0 ≤ Λ)
    (hstop : ∀ i,hi ≤ (Z i).stop) (hsmall : ∀ i,(Z i).target-r ≤ horizon n)
    (c : ι→Domain→ℝ) (hc : ∀ a,Measurable (c a)) (hell : 0<ell)
    (hb : ∀ a p,ell ≤ c a p ∧ c a p ≤ M) :
    ∀ᵐ y : HeatCircle ∂haarAddCircle,∀ a,
      weightedHeatRow Λ Z q r y∈(Matrix.toEuclideanCLM (𝕜:=ℝ)
        (stoppedCovariance (fun i=>(Z i).stop) (fun i=>(Z i).target) (fun i=>(Z i).center) (c a) q)).range ∧
      sqrt (scoreVariance (stoppedCovariance (fun i=>(Z i).stop) (fun i=>(Z i).target)
          (fun i=>(Z i).center) (c a) q) (weightedHeatRow Λ Z q r y)) ≤ 
        exp (-Λ*(r-q))*sqrt (constant n/(ell*(hi-r)))*∑ i,sqrt ‖ProfileVariance.heatPhysical
          (4*((Z i).target-r)) (Z i).center y‖ := by
  filter_upwards [weighted_all_profiles_ae Z hages (hq.trans hqr) le_rfl hrhi hΛ hstop hsmall c hc hell hb]
    with y hy
  intro a
  have hcb (p : Domain) : 0 ≤ c a p ∧ c a p ≤ M := ⟨hell.le.trans (hb a p).1,(hb a p).2⟩
  have hrange := range_mono_lower _ _ _ hages (c a) (hc a) hcb hq hqr (hy a).1
  have hscore := score_antitone_lower _ _ _ hages (c a) (hc a) hcb hq hqr (hy a).1
  rw [weighted_row_factor]
  refine ⟨Submodule.smul_mem _ _ hrange,?_⟩
  rw [scoreVariance_smul,sqrt_mul (sq_nonneg _),sqrt_sq_eq_abs,abs_of_pos (exp_pos _)]
  have hh := mul_le_mul_of_nonneg_left ((sqrt_le_sqrt hscore).trans (hy a).2) (exp_pos (-Λ*(r-q))).le
  simpa only [mul_assoc] using hh

end SHE.UniformFutureProfileScores
