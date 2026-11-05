module

public import SHE.PhysicalPointRowRange
public import SHE.IntervalScoreHeatKernel
public import SHE.NativeHeatDilation

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 2400000
noncomputable section

namespace SHE.PhysicalFirstScore
open Set Filter MeasureTheory StoppedFourier WordRecursion StoppedGaussianFeatures
  OldIntervalCovariance PhysicalScoreChain MeasurableGaussianScores
open scoped BigOperators
local instance : Fact (0 < 2*Real.pi) := ⟨by positivity⟩
attribute [local irreducible] MeasurableGaussianScores.coefficient
  MeasurableGeneralizedInverse.generalizedInverse

/-- The terminal point score has the true physical parent heat envelope,
with age four ready for the old-space forest integration. -/
theorem terminal_heat_envelope (n : ℕ) :
    ∃ H C : ℝ, 0 < H ∧ 0 < C ∧
    ∀ (Z : Fin n → Observation), (∀ i,(Z i).stop ≤ (Z i).target) →
    ∀ {lo hi ell M : ℝ}, 0 ≤ lo → lo < hi → (∀ i,hi ≤ (Z i).stop) →
    (∀ i,(Z i).target-lo ≤ H) →
    ∀ (c : Domain → ℝ), Measurable c → 0 < ell → (∀ r,ell ≤ c r ∧ c r ≤ M) →
    ∀ᵐ y : HeatCircle ∂AddCircle.haarAddCircle,
      scoreVariance (intervalCovariance Z c lo hi) (heatRow Z lo y) ≤
        C/(ell*(hi-lo))*∑ i : Fin n,‖ProfileVariance.heatPhysical (4*((Z i).target-lo)) (Z i).center y‖ := by
  obtain ⟨H,C,hH,hC,hV⟩ := IntervalScoreEnvelope.score_heat_kernel n
  refine ⟨H,C*Real.sqrt 2,hH,by positivity,?_⟩
  intro Z hages lo hi ell M hlo hgap hstop hsmall c hc hell hb
  let σ := fun i => (Z i).stop
  let target := fun i => (Z i).target
  let center := fun i => (Z i).center
  have hactive : IntervalHistoryEnergy.active σ hi=Finset.univ := by
    apply Finset.filter_eq_self.mpr
    intro i _
    exact hstop i
  have hrow (y : HeatCircle) : heatRow Z lo y=stoppedRow σ target center (lo,y) := by
    ext i
    change (ProfileVariance.heatPhysical ((Z i).target-lo) (Z i).center y).re =
      if lo < (Z i).stop then (ProfileVariance.heatPhysical ((Z i).target-lo) (Z i).center y).re else 0
    rw [ite_eq_left (hgap.trans_le (hstop i))]
  have hh := hV σ target center hages hlo hgap (fun i => Or.inr (hstop i))
    (fun i _ => hsmall i) c hc hell hb
  filter_upwards [hh] with y hy
  rw [hrow]
  have hsum : (∑ i : Fin n,‖ProfileVariance.heatPhysical (2*((Z i).target-lo)) (Z i).center y‖) ≤
      Real.sqrt 2*∑ i : Fin n,‖ProfileVariance.heatPhysical (4*((Z i).target-lo)) (Z i).center y‖ := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun i _ => NativeHeatSpan.physical_two_le_four
      (by linarith [hstop i,hages i] : 0 < (Z i).target-lo) (Z i).center y)
  simp only [hactive] at hy
  have hz := hy.trans (mul_le_mul_of_nonneg_left hsum
    (div_nonneg hC.le (mul_nonneg hell.le (sub_pos.mpr hgap).le)))
  change scoreVariance (stoppedCovariance σ target center (intervalProfile c lo hi) 0)
    (stoppedRow σ target center (lo,y)) ≤ _
  convert! hz using 1 <;> ring

theorem sqrt_sum_le {ι : Type*} [Fintype ι] (f : ι → ℝ) (hf : ∀ i,0 ≤ f i) :
    Real.sqrt (∑ i,f i) ≤ ∑ i,Real.sqrt (f i) := by
  apply Real.sqrt_le_iff.mpr
  refine ⟨Finset.sum_nonneg (fun i _ => Real.sqrt_nonneg _),?_⟩
  have hh (i : ι) : Real.sqrt (f i) ≤ ∑ j,Real.sqrt (f j) :=
    Finset.single_le_sum (fun j _ => Real.sqrt_nonneg _) (Finset.mem_univ i)
  have hs := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset ι)) =>
    mul_le_mul_of_nonneg_left (hh i) (Real.sqrt_nonneg (f i)))
  rw [←Finset.sum_mul] at hs
  simpa only [←pow_two,Real.sq_sqrt (hf _)] using hs

/-- First-score normalization keeps exactly the square root of the fresh
interval cost and one sum of square-root physical terminal heat edges. -/
theorem terminal_sqrt_heat_envelope (n : ℕ) :
    ∃ H C : ℝ, 0 < H ∧ 0 < C ∧
    ∀ (Z : Fin n → Observation), (∀ i,(Z i).stop ≤ (Z i).target) →
    ∀ {lo hi ell M : ℝ}, 0 ≤ lo → lo < hi → (∀ i,hi ≤ (Z i).stop) →
    (∀ i,(Z i).target-lo ≤ H) →
    ∀ (c : Domain → ℝ), Measurable c → 0 < ell → (∀ r,ell ≤ c r ∧ c r ≤ M) →
    ∀ᵐ y : HeatCircle ∂AddCircle.haarAddCircle,
      Real.sqrt (scoreVariance (intervalCovariance Z c lo hi) (heatRow Z lo y)) ≤
        Real.sqrt (C/(ell*(hi-lo)))*
          ∑ i : Fin n,Real.sqrt ‖ProfileVariance.heatPhysical (4*((Z i).target-lo)) (Z i).center y‖ := by
  obtain ⟨H,C,hH,hC,hV⟩ := terminal_heat_envelope n
  refine ⟨H,C,hH,hC,?_⟩
  intro Z hages lo hi ell M hlo hgap hstop hsmall c hc hell hb
  filter_upwards [hV Z hages hlo hgap hstop hsmall c hc hell hb] with y hy
  have hh := Real.sqrt_le_sqrt hy
  rw [Real.sqrt_mul (div_nonneg hC.le (mul_nonneg hell.le (sub_pos.mpr hgap).le))] at hh
  exact hh.trans (mul_le_mul_of_nonneg_left (sqrt_sum_le _ (fun _ => norm_nonneg _)) (Real.sqrt_nonneg _))

end SHE.PhysicalFirstScore
