module

public import SHE.ScalarHeatBandJets

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
namespace SHE.ScalarHeatBandBernstein
open Set MeasureTheory Real GaussianAudit SmoothCylinders ScalarGaussianSemigroup ScalarGaussianJetScale ScalarHeatBands
open scoped NNReal ENNReal

def amplitude (B H β : ℝ) (k : ℕ) : ℝ:=
  |B|+3*H*gaussianAbsMoment β+2*H*(∑ n∈Finset.range (k+1),constant β n)

theorem amplitude_nonneg {B H β : ℝ} (hH : 0≤H) (k : ℕ) : 0≤amplitude B H β k:=by
  have hsum : 0≤∑ n∈Finset.range (k+1),constant β n:=
    Finset.sum_nonneg (fun n _=>constant_nonneg β n)
  dsimp only [amplitude]
  exact add_nonneg (add_nonneg (abs_nonneg _) (mul_nonneg (mul_nonneg (by norm_num) hH) (gaussianAbsMoment_nonneg _)))
    (mul_nonneg (mul_nonneg (by norm_num) hH) hsum)

theorem amplitude_bounds {B H β : ℝ} (hH : 0≤H) (k : ℕ) :
    |B|≤amplitude B H β k ∧ 3*(H*gaussianAbsMoment β)≤amplitude B H β k:=by
  have hsum : 0≤∑ n∈Finset.range (k+1),constant β n:=
    Finset.sum_nonneg (fun n _=>constant_nonneg β n)
  dsimp only [amplitude]
  constructor <;> nlinarith [abs_nonneg B,mul_nonneg hH (gaussianAbsMoment_nonneg β),mul_nonneg hH hsum]

theorem amplitude_jet {B H β : ℝ} (hH : 0≤H) {k n : ℕ} (hn : n≤k) :
    2*H*constant β n≤amplitude B H β k:=by
  have hs : constant β n≤∑ i∈Finset.range (k+1),constant β i:=
    Finset.single_le_sum (fun i _=>constant_nonneg β i) (Finset.mem_range.mpr (by omega))
  dsimp only [amplitude]
  nlinarith [mul_le_mul_of_nonneg_left hs (by positivity : 0≤2*H),abs_nonneg B,
    mul_nonneg hH (gaussianAbsMoment_nonneg β)]

/-- The SAME actual heat bands used for future-variance cancellation
satisfy every fixed finite jet hypothesis of the existing scalar
finite-word/root comparison. One amplitude is independent of band and
of every unsmoothed coefficient derivative. -/
theorem all_jets {a : ℝ→ℝ} (ha : BoundedSmooth a) {B H β : ℝ}
    (hB : ∀ x,|a x|≤B) (hH : 0≤H) (hβ : 0≤β) (hβ1 : β≤1)
    (hh : ∀ x y,|a x-a y|≤H*|x-y|^β) (k j n : ℕ) (hn : n≤k) (x : ℝ) :
    ‖iteratedFDeriv ℝ n (band a j) x‖≤
      (amplitude B H β k*((2:ℝ)^j)^(-β))*((2:ℝ)^j)^n := by
  have hp : 0≤CompactMollifier.radius j^(β-(n:ℝ)):=rpow_nonneg (CompactMollifier.radius_pos j).le _
  have hb : |iteratedDeriv n (band a j) x|≤amplitude B H β k*CompactMollifier.radius j^(β-(n:ℝ)):=by
    cases n with
    | zero =>
      simp only [iteratedDeriv_zero,Nat.cast_zero,sub_zero]
      cases j with
      | zero =>
        have hs:=heat_bound (variance 0) hB x
        exact (by simpa only [band,smooth,CompactMollifier.radius,pow_zero,Real.one_rpow,mul_one] using
          hs.trans ((le_abs_self B).trans (amplitude_bounds (B:=B) (β:=β) hH k).1))
      | succ j =>
        exact (band_succ_bound ha.smooth.continuous.measurable hB hH hβ hβ1 hh j x).trans
          (mul_le_mul_of_nonneg_right (amplitude_bounds (B:=B) (β:=β) hH k).2
            (rpow_nonneg (CompactMollifier.radius_pos (j+1)).le _))
    | succ n =>
      have hh':=ScalarHeatBandJets.positive_jet ha hH hβ hβ1 hh j n x
      have hc:=amplitude_jet (B:=B) (β:=β) hH (show n≤k by omega)
      have he : β-(n:ℝ)-1=β-((n+1:ℕ):ℝ):=by push_cast; ring
      rw [he] at hh'
      exact hh'.trans (mul_le_mul_of_nonneg_right hc hp)
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv,Real.norm_eq_abs]
  simpa only [ScalarDyadicBands.radius_frequency,mul_assoc] using hb

end SHE.ScalarHeatBandBernstein
