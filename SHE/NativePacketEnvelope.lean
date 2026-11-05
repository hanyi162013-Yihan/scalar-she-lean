module

public import SHE.NativeFirstWholeComplete
public import SHE.TwoFreshCompleteWord
public import SHE.TwoFreshOffsetAffine

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

namespace SHE.NativePacketEnvelope
open MeasureTheory Real GaussianAssignmentBlocks
open scoped BigOperators
variable {m r : ℕ}

theorem rpow_affine {a b θ p : ℝ} (hθ : θ∈Set.Icc (0:ℝ) 1) (hp : 0≤p) :
    |(1-θ)*a+θ*b|^p≤(2:ℝ)^p*(|a|^p+|b|^p) := by
  have h : |(1-θ)*a+θ*b|≤|a|+|b| := by
    calc
      _≤|(1-θ)*a|+|θ*b| := abs_add_le _ _
      _=(1-θ)*|a|+θ*|b| := by
        rw [abs_mul,abs_mul,abs_of_nonneg (sub_nonneg.mpr hθ.2),abs_of_nonneg hθ.1]
      _≤|a|+|b| := add_le_add
        (mul_le_of_le_one_left (abs_nonneg _) (by linarith [hθ.1]))
        (mul_le_of_le_one_left (abs_nonneg _) hθ.2)
  apply (rpow_le_rpow (abs_nonneg _) h hp).trans
  by_cases hab : |a|≤|b|
  · calc
      (|a|+|b|)^p≤(2*|b|)^p := rpow_le_rpow (by positivity) (by linarith) hp
      _=(2:ℝ)^p*|b|^p := mul_rpow (by norm_num) (abs_nonneg _)
      _≤(2:ℝ)^p*(|a|^p+|b|^p) := mul_le_mul_of_nonneg_left
        (le_add_of_nonneg_left (rpow_nonneg (abs_nonneg _) _)) (by positivity)
  · have hab' : |b|≤|a| := le_of_not_ge hab
    calc
      (|a|+|b|)^p≤(2*|a|)^p := rpow_le_rpow (by positivity) (by linarith) hp
      _=(2:ℝ)^p*|a|^p := mul_rpow (by norm_num) (abs_nonneg _)
      _≤(2:ℝ)^p*(|a|^p+|b|^p) := mul_le_mul_of_nonneg_left
        (le_add_of_nonneg_right (rpow_nonneg (abs_nonneg _) _)) (by positivity)

/-- One endpoint packet controls every interpolated current offset,
at the original native ages. -/
theorem budget_interpolate (age a b : Fin m→ℝ) (θ p degree : ℝ)
    (hage : ∀j,0<age j) (hθ : θ∈Set.Icc (0:ℝ) 1) (hp : 0≤p) :
    NormalizedLeafOffsets.budget age (fun j=>(1-θ)*a j+θ*b j) p degree≤
      (2:ℝ)^p*(NormalizedLeafOffsets.budget age a p degree+
        NormalizedLeafOffsets.budget age b p degree) := by
  unfold NormalizedLeafOffsets.budget
  rw [←Finset.sum_add_distrib,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j _
  have hh:=div_le_div_of_nonneg_right (rpow_affine (a:=a j) (b:=b j) hθ hp)
    (rpow_nonneg (hage j).le degree)
  convert! hh using 1 <;> ring

private theorem affine_bound {a s c : ℝ} (ha : 0≤a) (hs : 0≤s) (hc : 0≤c) :
    a+s*c≤(a+s)*(1+c) := by
  nlinarith [mul_nonneg ha hc]

theorem whole_constant (P : CanonicalCovariance.ProfileParameters) (b : ℕ)
    (choices : List (Fin r×Fin (m+1))) {c : ℝ} (hc : 0≤c) :
    NativeFirstWholeMoments.constant P r m choices b c≤
      NativeFirstWholeMoments.constant P r m choices b 1*(1+c) := by
  rw [NativeFirstWholeMoments.constant_affine,NativeFirstWholeMoments.constant_affine P b choices 1]
  simpa only [mul_one] using affine_bound
    (NativeFirstWholeMoments.constant_nonneg P b choices (by norm_num : (0:ℝ)≤0))
    (FullResidualAssignedMoments.offsetSlope_nonneg b choices) hc

theorem marked_constant (P : CanonicalCovariance.ProfileParameters) (b : ℕ)
    (choices : List (Fin r×Fin (m+1))) {c : ℝ} (hc : 0≤c) :
    TwoFreshFullResidualMoments.constant P r m choices b c≤
      TwoFreshFullResidualMoments.constant P r m choices b 1*(1+c) := by
  rw [TwoFreshFullResidualMoments.constant_affine,TwoFreshFullResidualMoments.constant_affine P b choices 1]
  simpa only [mul_one] using affine_bound
    (TwoFreshFullResidualMoments.constant_nonneg P b choices (by norm_num : (0:ℝ)≤0))
    (FullResidualAssignedMoments.offsetSlope_nonneg b choices) hc

theorem whole_momentConstant (P : CanonicalCovariance.ProfileParameters) (r m b : ℕ)
    {c : ℝ} (hc : 0≤c) :
    NativeFirstWholeComplete.momentConstant P r m b c≤
      NativeFirstWholeComplete.momentConstant P r m b 1*(1+c) := by
  let cs:=assignments (m:=m+1) (List.finRange r)
  have hs : (cs.map (fun choices=>max (NativeFirstWholeMoments.constant P r m choices b c) 0)).sum≤
      (cs.map (fun choices=>max (NativeFirstWholeMoments.constant P r m choices b 1) 0)).sum*(1+c) := by
    rw [←List.sum_map_mul_right]
    apply List.sum_le_sum
    intro choices _
    rw [max_eq_left (NativeFirstWholeMoments.constant_nonneg P b choices hc),
      max_eq_left (NativeFirstWholeMoments.constant_nonneg P b choices (by norm_num : (0:ℝ)≤1))]
    exact whole_constant P b choices hc
  have hh:=mul_le_mul_of_nonneg_left hs
    (show 0≤((1/2:ℝ)^r)^(2*b)*(cs.length:ℝ)^(2*b-1) by positivity)
  simpa only [NativeFirstWholeComplete.momentConstant,cs,mul_assoc] using hh

theorem marked_momentConstant (P : CanonicalCovariance.ProfileParameters) (r m b : ℕ)
    {c : ℝ} (hc : 0≤c) :
    TwoFreshCompleteWord.momentConstant P r m b c≤
      TwoFreshCompleteWord.momentConstant P r m b 1*(1+c) := by
  let cs:=assignments (m:=m+1) (List.finRange r)
  have hs : (cs.map (fun choices=>max (TwoFreshFullResidualMoments.constant P r m choices b c) 0)).sum≤
      (cs.map (fun choices=>max (TwoFreshFullResidualMoments.constant P r m choices b 1) 0)).sum*(1+c) := by
    rw [←List.sum_map_mul_right]
    apply List.sum_le_sum
    intro choices _
    rw [max_eq_left (TwoFreshFullResidualMoments.constant_nonneg P b choices hc),
      max_eq_left (TwoFreshFullResidualMoments.constant_nonneg P b choices (by norm_num : (0:ℝ)≤1))]
    exact marked_constant P b choices hc
  have hh:=mul_le_mul_of_nonneg_left hs
    (show 0≤((1/2:ℝ)^r)^(2*b)*(cs.length:ℝ)^(2*b-1) by positivity)
  simpa only [TwoFreshCompleteWord.momentConstant,cs,mul_assoc] using hh

end SHE.NativePacketEnvelope
