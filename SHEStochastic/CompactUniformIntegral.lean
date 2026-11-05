module

public import Mathlib.MeasureTheory.Measure.Tight
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.Topology.UniformSpace.UniformConvergence

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
noncomputable section

namespace SHEStochastic.CompactUniformIntegral
open MeasureTheory Filter Set
open scoped Topology ENNReal
variable {E : Type*} [TopologicalSpace E] [T2Space E] [MeasurableSpace E] [BorelSpace E]

/-- Split a bounded integral error over a compact set and its complement. -/
theorem error_bound (μ : Measure E) [IsProbabilityMeasure μ]
    (f g : BoundedContinuousFunction E ℝ) (K : Set E) (hK : MeasurableSet K)
    (ε B : ℝ) (hε : 0≤ε) (hlocal : ∀ x∈K,‖f x-g x‖≤ε)
    (hglobal : ∀ x,‖f x-g x‖≤B) :
    ‖(∫ x,f x ∂μ)-(∫ x,g x ∂μ)‖≤ε+B*μ.real Kᶜ := by
  have hi : Integrable (fun x => f x-g x) μ := (f.integrable μ).sub (g.integrable μ)
  rw [←integral_sub (f.integrable μ) (g.integrable μ),←integral_add_compl hK hi]
  calc
    _ ≤ ‖∫ x in K,f x-g x ∂μ‖+‖∫ x in Kᶜ,f x-g x ∂μ‖ := norm_add_le _ _
    _ ≤ ε*μ.real K+B*μ.real Kᶜ := add_le_add
      (norm_setIntegral_le_of_norm_le_const (measure_lt_top μ K) hlocal)
      (norm_setIntegral_le_of_norm_le_const (measure_lt_top μ Kᶜ) (fun x _ => hglobal x))
    _ ≤ ε+B*μ.real Kᶜ := add_le_add
      (by simpa only [mul_one] using
        mul_le_mul_of_nonneg_left (measureReal_le_one (μ := μ) (s := K)) hε) le_rfl

/-- Compact-uniform convergence of uniformly bounded tests suffices
for their integral error to vanish under a tight, varying family of laws. -/
theorem error_tendsto (P : ℕ → ProbabilityMeasure E)
    (hTight : IsTightMeasureSet (Set.range (fun m => (P m).toMeasure)))
    (f : ℕ → BoundedContinuousFunction E ℝ) (g : BoundedContinuousFunction E ℝ)
    (B : ℝ) (hB : 0≤B) (hf : ∀ m x,‖f m x‖≤B) (hg : ∀ x,‖g x‖≤B)
    (hlim : ∀ K : Set E,IsCompact K → TendstoUniformlyOn (fun m x => f m x) g atTop K) :
    Tendsto (fun m => (∫ x,f m x ∂(P m).toMeasure)-(∫ x,g x ∂(P m).toMeasure))
      atTop (𝓝 0) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  let δ : ℝ := ε/(8*(B+1))
  have hδ : 0<δ := by dsimp only [δ];positivity
  have hδsmall : 2*B*δ<ε/2 := by
    dsimp only [δ]
    rw [←mul_div_assoc,div_lt_iff₀ (by positivity : (0 : ℝ)<8*(B+1))]
    nlinarith
  obtain ⟨K,hK,hKtail⟩ :=
    (isTightMeasureSet_iff_exists_isCompact_measure_compl_le.mp hTight)
      (ENNReal.ofReal δ) (ENNReal.ofReal_pos.mpr hδ)
  obtain ⟨N,hN⟩ := eventually_atTop.mp
    ((Metric.tendstoUniformlyOn_iff.mp (hlim K hK)) (ε/2) (by positivity))
  refine ⟨N,fun m hm => ?_⟩
  have htail : (P m).toMeasure.real Kᶜ≤δ := by
    simpa only [Measure.real,ENNReal.toReal_ofReal hδ.le] using
      ENNReal.toReal_mono ENNReal.ofReal_ne_top (hKtail _ (Set.mem_range_self m))
  have hlocal : ∀ x∈K,‖f m x-g x‖≤ε/2 := by
    intro x hx
    have hh := hN m hm x hx
    simpa only [dist_eq_norm,norm_sub_rev] using hh.le
  have hb := error_bound (P m).toMeasure (f m) g K hK.isClosed.measurableSet
    (ε/2) (2*B) (by positivity) hlocal
    (fun x => (norm_sub_le (f m x) (g x)).trans (by linarith [hf m x,hg x]))
  rw [dist_zero_right]
  exact hb.trans_lt (by nlinarith [mul_le_mul_of_nonneg_left htail (show 0≤2*B by positivity)])

/-- The corresponding moving-test version of weak convergence. -/
theorem tendsto (P : ℕ → ProbabilityMeasure E) (Q : ProbabilityMeasure E)
    (hP : Tendsto P atTop (𝓝 Q))
    (hTight : IsTightMeasureSet (Set.range (fun m => (P m).toMeasure)))
    (f : ℕ → BoundedContinuousFunction E ℝ) (g : BoundedContinuousFunction E ℝ)
    (B : ℝ) (hB : 0≤B) (hf : ∀ m x,‖f m x‖≤B) (hg : ∀ x,‖g x‖≤B)
    (hlim : ∀ K : Set E,IsCompact K → TendstoUniformlyOn (fun m x => f m x) g atTop K) :
    Tendsto (fun m => ∫ x,f m x ∂(P m).toMeasure) atTop (𝓝 (∫ x,g x ∂Q.toMeasure)) := by
  have he := error_tendsto P hTight f g B hB hf hg hlim
  have hgP := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hP g
  simpa only [sub_add_cancel,zero_add] using he.add hgP

end SHEStochastic.CompactUniformIntegral
