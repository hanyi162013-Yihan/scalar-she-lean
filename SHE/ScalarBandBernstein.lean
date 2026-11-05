module

public import SHE.ScalarDyadicBands

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SHE.ScalarBandBernstein
open Set Filter Real MeasureTheory ScalarDyadicBands ScaledMollifierEstimates
open scoped ContDiff

def amplitude (B H : ℝ) (k : ℕ) : ℝ :=
  |B|+4*H+2*H*(∑ n∈Finset.range (k+1),jetConstant n)

theorem amplitude_nonneg {B H : ℝ} (hH : 0≤H) (k : ℕ) : 0≤amplitude B H k := by
  have hs : 0≤∑ n∈Finset.range (k+1),jetConstant n:=
    Finset.sum_nonneg (fun n _=>jetConstant_nonneg n)
  dsimp [amplitude]
  positivity

theorem amplitude_zero {B H : ℝ} (hH : 0≤H) (k : ℕ) :
    |B|+H≤amplitude B H k ∧ 3*H≤amplitude B H k := by
  have hs : 0≤∑ n∈Finset.range (k+1),jetConstant n:=
    Finset.sum_nonneg (fun n _=>jetConstant_nonneg n)
  dsimp [amplitude]
  constructor <;> nlinarith [abs_nonneg B,mul_nonneg hH hs]

theorem amplitude_jet {B H : ℝ} (hH : 0≤H) {k n : ℕ} (hn : n≤k) :
    2*H*jetConstant n≤amplitude B H k := by
  have hs : jetConstant n≤∑ j∈Finset.range (k+1),jetConstant j :=
    Finset.single_le_sum (fun j _=>jetConstant_nonneg j) (Finset.mem_range.mpr (by omega))
  have hh:=mul_le_mul_of_nonneg_left hs (by positivity : 0≤2*H)
  dsimp [amplitude]
  nlinarith [abs_nonneg B]

/-- Positive-order Bernstein estimate for the actual difference of
successive compact smoothings. The constant is independent of scale. -/
theorem positive_jet {a : ℝ→ℝ} (ha : Continuous a) {B H β : ℝ}
    (hB : ∀ x,|a x|≤B) (hH : 0≤H) (hβ : 0≤β) (hβ1 : β≤1)
    (hh : ∀ x y,|a x-a y|≤H*|x-y|^β) (j n : ℕ) (hn : 0<n) (x : ℝ) :
    ‖iteratedFDeriv ℝ n (band a j) x‖≤
      (2*H*jetConstant n)*CompactMollifier.radius j^(β-(n:ℝ)) := by
  have hcoef : 0≤H*jetConstant n:=mul_nonneg hH (jetConstant_nonneg n)
  have hsingle (l : ℕ) : ‖iteratedFDeriv ℝ n (smooth a l) x‖≤
      H*jetConstant n*CompactMollifier.radius l^(β-(n:ℝ)) :=
    mollify_jet_holder ha hB hH hβ (CompactMollifier.radius_pos l) hh n hn x
  cases j with
  | zero =>
    change ‖iteratedFDeriv ℝ n (smooth a 0) x‖≤_
    have hp : 0≤H*jetConstant n*CompactMollifier.radius 0^(β-(n:ℝ)) :=
      mul_nonneg hcoef (rpow_nonneg (CompactMollifier.radius_pos 0).le _)
    exact (hsingle 0).trans (by nlinarith)
  | succ j =>
    have hn1 : (1:ℝ)≤n:=by exact_mod_cast (show 1≤n by omega)
    have hp:=Real.rpow_le_rpow_of_nonpos (CompactMollifier.radius_pos (j+1))
      (radius_antitone j) (by linarith : β-(n:ℝ)≤0)
    have hprev:=(hsingle j).trans (mul_le_mul_of_nonneg_left hp hcoef)
    change ‖iteratedFDeriv ℝ n (smooth a (j+1)-smooth a j) x‖≤_
    rw [iteratedFDeriv_sub_apply
      ((smooth_boundedSmooth ha hB (j+1)).smooth.of_le (by simp)).contDiffAt
      ((smooth_boundedSmooth ha hB j).smooth.of_le (by simp)).contDiffAt]
    exact (norm_sub_le _ _).trans ((add_le_add (hsingle (j+1)) hprev).trans_eq (by ring))

/-- A bounded scalar Holder coefficient has one genuine smooth band
family with all jets through any fixed finite order and one amplitude
independent of the band index. -/
theorem all_jets {a : ℝ→ℝ} (ha : Continuous a) {B H β : ℝ}
    (hB : ∀ x,|a x|≤B) (hH : 0≤H) (hβ : 0≤β) (hβ1 : β≤1)
    (hh : ∀ x y,|a x-a y|≤H*|x-y|^β) (k j n : ℕ) (hn : n≤k) (x : ℝ) :
    ‖iteratedFDeriv ℝ n (band a j) x‖≤
      (amplitude B H k*((2:ℝ)^j)^(-β))*((2:ℝ)^j)^n := by
  have hscale : 0≤CompactMollifier.radius j^(β-(n:ℝ)):=
    rpow_nonneg (CompactMollifier.radius_pos j).le _
  have hb : ‖iteratedFDeriv ℝ n (band a j) x‖≤
      amplitude B H k*CompactMollifier.radius j^(β-(n:ℝ)) := by
    by_cases hn0 : n=0
    · subst n
      rw [norm_iteratedFDeriv_zero]
      simp only [Nat.cast_zero,sub_zero]
      cases j with
      | zero =>
        have he:=smooth_error ha hB hH hβ hh 0 x
        have hb0: |smooth a 0 x|≤|B|+H:=by
          calc
            _≤|smooth a 0 x-a x|+|a x|:=by
              simpa only [sub_zero] using abs_sub_le (smooth a 0 x) (a x) (0:ℝ)
            _≤H+B:=by simpa only [CompactMollifier.radius,pow_zero,Real.one_rpow,mul_one] using add_le_add he (hB x)
            _≤|B|+H:=by linarith [le_abs_self B]
        simpa only [band,CompactMollifier.radius,pow_zero,Real.one_rpow,mul_one,Real.norm_eq_abs] using
          hb0.trans (amplitude_zero (B:=B) hH k).1
      | succ j =>
        have hb0:=band_succ_bound ha hB hH hβ hβ1 hh j x
        simpa only [Real.norm_eq_abs] using hb0.trans
          (mul_le_mul_of_nonneg_right (amplitude_zero (B:=B) hH k).2
            (rpow_nonneg (CompactMollifier.radius_pos (j+1)).le _))
    · exact (positive_jet ha hB hH hβ hβ1 hh j n (Nat.pos_of_ne_zero hn0) x).trans
        (mul_le_mul_of_nonneg_right (amplitude_jet (B:=B) hH hn) hscale)
  simpa only [radius_frequency,mul_assoc] using hb

end SHE.ScalarBandBernstein
