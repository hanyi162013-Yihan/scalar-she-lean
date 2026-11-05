module

public import SHE.RangeTerminalRepresentation

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section

namespace SHE.PhysicalFirstScore
open Set Filter MeasureTheory ProbabilityTheory AddCircle Real StoppedFourier WordRecursion
  StoppedGaussianFeatures OldIntervalCovariance PhysicalScoreChain
open scoped BigOperators
local instance : Fact (0<2*π) := ⟨by positivity⟩
variable {n : ℕ}

/-- The actual terminal point heat row lies in the actual old interval
covariance range almost everywhere in the input spatial point. Later
root targets are kept; clipping only the stop at the covered upper time
allows the genuine Gram/range theorem to apply. -/
theorem terminal_heatRow_mem_range_ae (Z : Fin n→Observation)
    {lo hi ell M : ℝ} (hlo : 0≤lo) (hgap : lo<hi) (hhi : hi≤1)
    (hstop : ∀ i,hi≤(Z i).stop) (hages : ∀ i,(Z i).stop≤(Z i).target)
    (c : Domain→ℝ) (hc : Measurable c) (hell : 0<ell)
    (hb : ∀ p,ell≤c p ∧ c p≤M) :
    ∀ᵐ x : HeatCircle ∂haarAddCircle,heatRow Z lo x∈
      (Matrix.toEuclideanCLM (𝕜:=ℝ) (intervalCovariance Z c lo hi)).range := by
  let σ : Fin n→ℝ := fun _ => hi
  let target : Fin n→ℝ := fun i => (Z i).target
  let center : Fin n→HeatCircle := fun i => (Z i).center
  have hσ : ∀ i,0<σ i := fun _ => hlo.trans_lt hgap
  have hσ1 : ∀ i,σ i≤1 := fun _ => hhi
  have hage : ∀ i,σ i≤target i := fun i => (hstop i).trans (hages i)
  have hm : intervalCovariance Z c lo hi=stoppedCovariance σ target center (intervalProfile c lo hi) 0 := by
    rw [StoppedWindowCovariance.interval_eq_clipped _ _ hlo]
    have he : (fun i => min (Z i).stop hi)=σ := funext (fun i => min_eq_right (hstop i))
    rw [he]
    symm
    have ht := StoppedWindowCovariance.interval_eq_clipped (fun i => ⟨hi,target i,center i⟩) c (hi:=hi) hlo
    simp only [min_self] at ht
    convert! ht using 1
  filter_upwards [OldIntervalCovariance.endpoint_row_mem_range_ae σ target center hσ hσ1 hage hlo hgap
    (fun _ => Or.inr le_rfl) c hc hell hb] with x hx
  rw [hm]
  convert! hx using 1
  ext i
  change (ProfileVariance.heatPhysical ((Z i).target-lo) (Z i).center x).re=
    if lo<hi then (ProfileVariance.heatPhysical ((Z i).target-lo) (Z i).center x).re else 0
  rw [if_pos hgap]

end SHE.PhysicalFirstScore
