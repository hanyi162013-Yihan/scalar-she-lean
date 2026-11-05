module

public import SHE.StandardTerminalIto
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

namespace SHE.PredictableSquareDominatedLimit
open Set MeasureTheory PredictableL2 Filter Topology
open scoped NNReal ENNReal
variable {Ω C : Type*} [MeasurableSpace Ω]
variable [NormedAddCommGroup C] [InnerProductSpace ℝ C]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) (H : ℝ≥0)

/-- Dominated convergence in the actual predictable L² space. The
majorant is a single square-integrable function on the original product
measure; no convergence of the chosen Lp representatives is postulated
outside one common almost-everywhere event. -/
theorem tendsto (U : ℕ→Process (E:=C) 𝓕 μ H) (V : Process (E:=C) 𝓕 μ H)
    (b : ℝ≥0×Ω→ℝ) (hb : Integrable b (energyMeasure μ H))
    (hU : ∀ n,∀ᵐ p ∂energyMeasure μ H,‖U n p‖^2≤b p)
    (hV : ∀ᵐ p ∂energyMeasure μ H,‖V p‖^2≤b p)
    (hlim : ∀ᵐ p ∂energyMeasure μ H,Tendsto (fun n=>U n p) atTop (𝓝 (V p))) :
    Tendsto U atTop (𝓝 V) := by
  have hmeas (n : ℕ) : AEStronglyMeasurable (fun p => ‖U n p-V p‖^2) (energyMeasure μ H) :=
    (((Lp.stronglyMeasurable (U n)).mono (predictable_le_product 𝓕)).sub
      ((Lp.stronglyMeasurable V).mono (predictable_le_product 𝓕))).norm.pow 2 |>.aestronglyMeasurable
  have hbound (n : ℕ) : ∀ᵐ p ∂energyMeasure μ H,‖‖U n p-V p‖^2‖≤4*b p := by
    filter_upwards [hU n,hV] with p hu hv
    rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
    have ht:=(pow_le_pow_left₀ (norm_nonneg _) (norm_sub_le (U n p) (V p)) 2).trans
      (add_pow_le (norm_nonneg (U n p)) (norm_nonneg (V p)) 2)
    norm_num only [Nat.reduceSub,pow_one] at ht
    nlinarith

  have ht := tendsto_integral_of_dominated_convergence (fun p=>4*b p) hmeas
    (hb.const_mul 4) hbound (hlim.mono (fun p hp => by
      simpa using (hp.sub tendsto_const_nhds).norm.pow 2))
  have hn : Tendsto (fun n=>‖U n-V‖^2) atTop (𝓝 0) := by
    have he (n : ℕ) : ‖U n-V‖^2=∫ p,‖U n p-V p‖^2 ∂energyMeasure μ H := by
      rw [subsigma_norm_sq]
      apply integral_congr_ae
      filter_upwards [ae_eq_of_ae_eq_trim (Lp.coeFn_sub (U n) V)] with p hp
      rw [hp]
      rfl
    simpa only [←he,sub_self,norm_zero,zero_pow (by norm_num : (2:ℕ)≠0),integral_zero] using ht
  have hn' := Real.continuous_sqrt.continuousAt.tendsto.comp hn
  have hn0 : Tendsto (fun n=>‖U n-V‖) atTop (𝓝 0) := by
    simpa only [Function.comp_def,Real.sqrt_sq_eq_abs,abs_norm,Real.sqrt_zero] using hn'
  apply tendsto_iff_dist_tendsto_zero.mpr
  simpa only [dist_eq_norm] using hn0

end SHE.PredictableSquareDominatedLimit
