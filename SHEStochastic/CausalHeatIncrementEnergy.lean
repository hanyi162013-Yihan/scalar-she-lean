module

public import SHE.HaarIncrementEnergy

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
noncomputable section

namespace SHEStochastic.CausalHeatIncrementEnergy
open MeasureTheory Set SHE SHE.PredictableL2
open scoped NNReal ENNReal
variable {P C : Type*} [NormedAddCommGroup C]

/-- The old/new-noise time split depends only on two deterministic
heat bounds. It is shared by scalar and matrix kernels, for arbitrary
time-dependent profiles and without stochastic independence. -/
theorem bound_small_increment (K : ℝ → P → C) (hzero : ∀ τ, τ ≤ 0 → ∀ q, K τ q=0)
    (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hsmall : ∀ τ, 0 < τ → τ ≤ 1 → ∀ q, ‖K τ q‖^2 ≤ A*τ^(-(1/2 : ℝ)))
    (hold : ∀ τ, 0 < τ → τ ≤ 1 → ∀ δ, 0 ≤ δ → δ ≤ 1 → ∀ q,
      ‖K (τ+δ) q-K τ q‖^2 ≤ B*δ^(1/4 : ℝ)*τ^(-(3/4 : ℝ)))
    {H s t : ℝ≥0} (hH : (H : ℝ) ≤ 1) (hst : s ≤ t) (htH : t ≤ H) (Q : ℝ≥0 → P) :
    (∫⁻ r, ENNReal.ofReal (‖K ((t : ℝ)-(r : ℝ)) (Q r)-K ((s : ℝ)-(r : ℝ)) (Q r)‖^2)
      ∂timeMeasure H) ≤ ENNReal.ofReal ((4*B+2*A)*((t : ℝ)-(s : ℝ))^(1/4 : ℝ)) := by
  let E (r : ℝ≥0) := ENNReal.ofReal
    (‖K ((t : ℝ)-(r : ℝ)) (Q r)-K ((s : ℝ)-(r : ℝ)) (Q r)‖^2)
  have hstR : (s : ℝ) ≤ t := by exact_mod_cast hst
  have htHR : (t : ℝ) ≤ H := by exact_mod_cast htH
  have hδ : 0 ≤ (t : ℝ)-(s : ℝ) := sub_nonneg.mpr hstR
  have hδ1 : (t : ℝ)-(s : ℝ) ≤ 1 := by linarith [s.2]
  have hzeroE : ∀ r, t < r → E r=0 := by
    intro r hr
    have htr : (t : ℝ) ≤ r := by exact_mod_cast hr.le
    simp only [E,hzero _ (sub_nonpos.mpr htr),hzero _ (sub_nonpos.mpr (hstR.trans htr)),
      sub_self,norm_zero,zero_pow (by decide : (2 : ℕ) ≠ 0),ENNReal.ofReal_zero]
  have ho : (∫⁻ r, E r ∂timeMeasure s) ≤
      ENNReal.ofReal (B*((t : ℝ)-(s : ℝ))^(1/4 : ℝ)*(4*(s : ℝ)^(1/4 : ℝ))) := by
    calc
      _ ≤ ∫⁻ r, ENNReal.ofReal (B*((t : ℝ)-(s : ℝ))^(1/4 : ℝ))*
          ENNReal.ofReal (((s : ℝ)-(r : ℝ))^(-(3/4 : ℝ))) ∂timeMeasure s := by
        apply lintegral_mono_ae
        filter_upwards [timeMeasure_ae_mem s,(timeMeasure s).ae_ne s] with r hr hrs
        have hrs' : r < s := lt_of_le_of_ne hr.2 hrs
        have hτ : 0 < (s : ℝ)-(r : ℝ) := sub_pos.mpr (by exact_mod_cast hrs')
        have hτ1 : (s : ℝ)-(r : ℝ) ≤ 1 := by linarith [r.2]
        have hb := hold _ hτ hτ1 _ hδ hδ1 (Q r)
        rw [show (s : ℝ)-r+((t : ℝ)-s)=(t : ℝ)-r by ring] at hb
        rw [← ENNReal.ofReal_mul (mul_nonneg hB (Real.rpow_nonneg hδ _))]
        exact ENNReal.ofReal_le_ofReal hb
      _ = _ := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
          causal_rpow_mass (by norm_num : (-1 : ℝ) < -(3/4 : ℝ))]
        norm_num only [show -(3/4 : ℝ)+1=1/4 by norm_num]
        rw [← ENNReal.ofReal_mul (mul_nonneg hB (Real.rpow_nonneg hδ _))]
        congr 1
        ring
  have hn : (∫⁻ r, E r ∂intervalTimeMeasure s t) ≤
      ENNReal.ofReal (A*(2*((t : ℝ)-(s : ℝ))^(1/2 : ℝ))) := by
    calc
      _ ≤ ∫⁻ r, ENNReal.ofReal A*ENNReal.ofReal (((t : ℝ)-(r : ℝ))^(-(1/2 : ℝ)))
          ∂intervalTimeMeasure s t := by
        apply lintegral_mono_ae
        filter_upwards [intervalTimeMeasure_ae_mem s htH] with r hr
        have hsr : (s : ℝ)-(r : ℝ) ≤ 0 := sub_nonpos.mpr (by exact_mod_cast hr.1.le)
        change E r ≤ _
        dsimp only [E]
        rw [hzero _ hsr,sub_zero,← ENNReal.ofReal_mul hA]
        apply ENNReal.ofReal_le_ofReal
        rcases lt_or_eq_of_le hr.2 with hrt | rfl
        · exact hsmall _ (sub_pos.mpr (by exact_mod_cast hrt)) (by linarith [r.2]) (Q r)
        · rw [sub_self,hzero _ le_rfl,norm_zero]
          simp
      _ = _ := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
          interval_causal_rpow_mass (by norm_num : (-1 : ℝ) < -(1/2 : ℝ)) hst]
        norm_num only [show -(1/2 : ℝ)+1=1/2 by norm_num]
        rw [← ENNReal.ofReal_mul hA]
        congr 1
        ring
  have hs1 : (s : ℝ)^(1/4 : ℝ) ≤ 1 := Real.rpow_le_one s.2 (hstR.trans (htHR.trans hH)) (by norm_num)
  have hd : ((t : ℝ)-(s : ℝ))^(1/2 : ℝ) ≤ ((t : ℝ)-(s : ℝ))^(1/4 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_ge' hδ hδ1 (by norm_num) (by norm_num)
  have hp : 0 ≤ ((t : ℝ)-(s : ℝ))^(1/4 : ℝ) := Real.rpow_nonneg hδ _
  have ho' : B*((t : ℝ)-(s : ℝ))^(1/4 : ℝ)*(4*(s : ℝ)^(1/4 : ℝ)) ≤
      4*B*((t : ℝ)-(s : ℝ))^(1/4 : ℝ) := by
    nlinarith [mul_le_mul_of_nonneg_left hs1 (mul_nonneg hB hp)]
  have hn' : A*(2*((t : ℝ)-(s : ℝ))^(1/2 : ℝ)) ≤ 2*A*((t : ℝ)-(s : ℝ))^(1/4 : ℝ) := by
    nlinarith [mul_le_mul_of_nonneg_left hd hA]
  change (∫⁻ r, E r ∂timeMeasure H) ≤ _
  rw [causal_lintegral_of_zero htH _ hzeroE,timeMeasure_split hst,lintegral_add_measure]
  exact (add_le_add (ho.trans (ENNReal.ofReal_le_ofReal ho'))
    (hn.trans (ENNReal.ofReal_le_ofReal hn'))).trans_eq (by
      rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
      congr 1
      ring)


/-- Backwards-compatible form for kernels whose old-noise bound is valid
for every nonnegative increment. -/
theorem bound (K : ℝ → P → C) (hzero : ∀ τ, τ ≤ 0 → ∀ q, K τ q=0)
    (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hsmall : ∀ τ, 0 < τ → τ ≤ 1 → ∀ q, ‖K τ q‖^2 ≤ A*τ^(-(1/2 : ℝ)))
    (hold : ∀ τ, 0 < τ → τ ≤ 1 → ∀ δ, 0 ≤ δ → ∀ q,
      ‖K (τ+δ) q-K τ q‖^2 ≤ B*δ^(1/4 : ℝ)*τ^(-(3/4 : ℝ)))
    {H s t : ℝ≥0} (hH : (H : ℝ) ≤ 1) (hst : s ≤ t) (htH : t ≤ H) (Q : ℝ≥0 → P) :
    (∫⁻ r, ENNReal.ofReal (‖K ((t : ℝ)-(r : ℝ)) (Q r)-K ((s : ℝ)-(r : ℝ)) (Q r)‖^2)
      ∂timeMeasure H) ≤ ENNReal.ofReal ((4*B+2*A)*((t : ℝ)-(s : ℝ))^(1/4 : ℝ)) :=
  bound_small_increment K hzero A B hA hB hsmall
    (fun τ hτ hτ1 δ hδ _ q => hold τ hτ hτ1 δ hδ q) hH hst htH Q

end SHEStochastic.CausalHeatIncrementEnergy
