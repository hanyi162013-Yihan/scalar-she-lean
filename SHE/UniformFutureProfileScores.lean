module

public import SHE.FullFutureWeightedScore
public import SHE.StoppedCovarianceOrder

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section

namespace SHE.UniformFutureProfileScores
open Set Filter MeasureTheory AddCircle Real StoppedFourier StoppedGaussianFeatures
  GaussianIncrement MeasurableGaussianScores WordRecursion StopWeightedRows
open scoped BigOperators
local instance uniformFutureProfileScores_periodPositive : Fact (0<2*π) := ⟨by positivity⟩
variable {ι : Type*} {n : ℕ}

def horizon (n : ℕ) : ℝ := Classical.choose (FullFutureDampedHeat.weighted_sqrt_heat_envelope n)
def constant (n : ℕ) : ℝ := Classical.choose (Classical.choose_spec (FullFutureDampedHeat.weighted_sqrt_heat_envelope n))
theorem horizon_pos (n : ℕ) : 0<horizon n :=
  (Classical.choose_spec (Classical.choose_spec (FullFutureDampedHeat.weighted_sqrt_heat_envelope n))).1
theorem constant_pos (n : ℕ) : 0<constant n :=
  (Classical.choose_spec (Classical.choose_spec (FullFutureDampedHeat.weighted_sqrt_heat_envelope n))).2.1

/-- One genuine spatial event controls the full q-law for ALL elliptic
future profiles, even an uncountable past-dependent family. Its physical
row is at r and its stop-dependent damping remains anchored at q. -/
theorem weighted_all_profiles_ae (Z : Fin n→Observation)
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
        sqrt (constant n/(ell*(hi-r)))*∑ i,sqrt ‖ProfileVariance.heatPhysical
          (4*((Z i).target-r)) (Z i).center y‖ := by
  have hbase := (Classical.choose_spec (Classical.choose_spec
    (FullFutureDampedHeat.weighted_sqrt_heat_envelope n))).2.2 Z hages hq hqr hrhi hΛ hstop hsmall
      (fun _=>ell) measurable_const hell (fun _=>⟨le_rfl,le_rfl⟩)
  filter_upwards [hbase] with y hy
  intro a
  have hb0 (p : Domain) : 0 ≤ ell ∧ ell ≤ ell := ⟨hell.le,le_rfl⟩
  have hb1 (p : Domain) : 0 ≤ c a p ∧ c a p ≤ M := ⟨hell.le.trans (hb a p).1,(hb a p).2⟩
  have hrange := StoppedCovarianceOrder.range_mono _ _ _ hages q (fun _=>ell) (c a)
    measurable_const (hc a) hb0 hb1 (fun p=>(hb a p).1) hy.1
  have hscore := StoppedCovarianceOrder.scoreVariance_antitone _ _ _ hages q (fun _=>ell) (c a)
    measurable_const (hc a) hb0 hb1 (fun p=>(hb a p).1) hy.1
  exact ⟨hrange,(sqrt_le_sqrt hscore).trans hy.2⟩

end SHE.UniformFutureProfileScores
