module

public import SHEStochastic.UnboundedGlobalJointMoments
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section

namespace SHEStochastic.SublinearHeatMomentScale
open MeasureTheory Filter
open scoped NNReal ENNReal Topology
variable {E V : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]

/-- The existing joint heat bracket constant factors into a fixed
coefficient/time constant and the explicit sublinear state factor. -/
theorem joint_factor (G : E → V) (C β : ℝ≥0) (hβ : 0<β) (K : ℝ) (H : ℝ≥0) :
    UnboundedGlobalJointMoments.jointConstant G C β K H=
      UnboundedGlobalJointMoments.jointConstant G C β 0 H*
        SublinearHeatIntegratedEnergy.stateFactor K β := by
  have hbr : (0 : ℝ)<β := hβ
  have hz : SublinearHeatIntegratedEnergy.stateFactor 0 β=1 := by
    simp only [SublinearHeatIntegratedEnergy.stateFactor,zero_pow (by norm_num : 2≠0),
      ENNReal.ofReal_zero,ENNReal.zero_rpow_of_pos hbr,add_zero]
  simp only [UnboundedGlobalJointMoments.jointConstant,UnboundedGlobalIncrementCaps.timeConstant,
    UnboundedGlobalIncrementCaps.spaceConstant,hz,mul_one]
  ring

/-- Exact radius dependence of the normalized sublinear energy. -/
theorem normalized_eq (β : ℝ≥0) (N : ℕ) (hN : 1≤N) :
    SublinearHeatIntegratedEnergy.stateFactor (N : ℝ) β/(N : ℝ≥0∞)^2=
      (N : ℝ≥0∞)^(-2 : ℝ)+(N : ℝ≥0∞)^(2*(β : ℝ)-2) := by
  have hn : (N : ℝ≥0∞)≠0 := by exact_mod_cast (ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one hN))
  have ht : (N : ℝ≥0∞)≠⊤ := by simp
  have hof : ENNReal.ofReal ((N : ℝ)^2)=(N : ℝ≥0∞)^2 := by
    rw [ENNReal.ofReal_pow (Nat.cast_nonneg N),ENNReal.ofReal_natCast]
  simp only [SublinearHeatIntegratedEnergy.stateFactor,hof,ENNReal.add_div]
  rw [ENNReal.rpow_sub _ _ hn ht,show (2 : ℝ)*(β : ℝ)=(2 : ℕ)*(β : ℝ) by norm_num,ENNReal.rpow_natCast_mul]
  simp only [ENNReal.rpow_neg,ENNReal.rpow_natCast,one_div]
  rw [ENNReal.rpow_two]

/-- Explicit polynomial decay at every chosen moment order. This is
stronger than mere vanishing and gives integrable exit-tail envelopes. -/
theorem normalized_bound (β : ℝ≥0) (N : ℕ) (hN : 1≤N) (p : ℕ) :
    (SublinearHeatIntegratedEnergy.stateFactor (N : ℝ) β/(N : ℝ≥0∞)^2)^p≤
      (2 : ℝ≥0∞)^p*(N : ℝ≥0∞)^((2*(β : ℝ)-2)*(p : ℝ)) := by
  rw [normalized_eq β N hN]
  have hn : (1 : ℝ≥0∞)≤N := by exact_mod_cast hN
  have he : (N : ℝ≥0∞)^(-2 : ℝ)≤(N : ℝ≥0∞)^(2*(β : ℝ)-2) :=
    ENNReal.rpow_le_rpow_of_exponent_le hn (by linarith [β.property])
  calc
    _ ≤ ((N : ℝ≥0∞)^(2*(β : ℝ)-2)+(N : ℝ≥0∞)^(2*(β : ℝ)-2))^p :=
      pow_le_pow_left' (add_le_add he le_rfl) p
    _ = _ := by
      rw [←two_mul,mul_pow]
      congr 1
      simpa only [ENNReal.rpow_natCast] using
        (ENNReal.rpow_mul (N : ℝ≥0∞) (2*(β : ℝ)-2) (p : ℝ)).symm

/-- The localized sublinear moment growth is negligible relative to
its exit threshold, at every positive even-moment order. This is the
radius-decay factor needed for uniform nonexplosion, not an assumed
solution moment bound. -/
theorem normalized_tendsto (β : ℝ≥0) (hβ1 : β<1) (p : ℕ) (hp : 0<p) :
    Tendsto (fun N : ℕ => (SublinearHeatIntegratedEnergy.stateFactor (N : ℝ) β/(N : ℝ≥0∞)^2)^p)
      atTop (𝓝 0) := by
  have hβr : (β : ℝ)<1 := hβ1
  have hneg : 2*(β : ℝ)-2<0 := by linarith
  have h1 : Tendsto (fun N : ℕ => (N : ℝ≥0∞)^(-2 : ℝ)) atTop (𝓝 0) := by
    simpa only [Function.comp_def,ENNReal.top_rpow_of_neg (by norm_num : (-2 : ℝ)<0)] using
      (ENNReal.continuous_rpow_const (y := (-2 : ℝ))).tendsto ⊤ |>.comp ENNReal.tendsto_nat_nhds_top
  have h2 : Tendsto (fun N : ℕ => (N : ℝ≥0∞)^(2*(β : ℝ)-2)) atTop (𝓝 0) := by
    simpa only [Function.comp_def,ENNReal.top_rpow_of_neg hneg] using
      (ENNReal.continuous_rpow_const (y := 2*(β : ℝ)-2)).tendsto ⊤ |>.comp ENNReal.tendsto_nat_nhds_top
  have hlim : Tendsto (fun N : ℕ => ((N : ℝ≥0∞)^(-2 : ℝ)+(N : ℝ≥0∞)^(2*(β : ℝ)-2))^p)
      atTop (𝓝 0) := by
    simpa only [add_zero,zero_pow (Nat.ne_of_gt hp)] using ENNReal.Tendsto.pow (n := p) (h1.add h2)
  apply hlim.congr'
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with N hN
  congr 1
  exact (normalized_eq β N hN).symm

end SHEStochastic.SublinearHeatMomentScale
