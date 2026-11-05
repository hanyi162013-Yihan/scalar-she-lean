module

public import SHE.MixedPastWordMoments
public import SHE.BaselineOriginalGain

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SHE.NativeOmittedTimeTotal
open Set Real GaussianAssignmentBlocks StoppedFourier
open scoped BigOperators
variable {d r m:ℕ}

def factor (P:CanonicalCovariance.ProfileParameters) (lo hi:Fin r→ℝ) (age:Fin m→ℝ)
    (cs:List (Fin r×Fin (m+1))) (j0:Fin m) (A0 ν:ℝ):ℝ:=
  if block cs j0.succ=[] then
    VectorPhysicalRoot.scale cs 0 lo hi A0 ν (P.lower/2) d*
      ∏j∈Finset.univ.erase j0,NativeAssignedLeafMoments.leafScale P cs j.succ lo hi (age j)
        (MinimumGapChoice.blockChoice lo hi cs j.succ)
  else 0

def total (P:CanonicalCovariance.ProfileParameters) (lo hi:Fin r→ℝ) (age:Fin m→ℝ)
    (j0:Fin m) (A0 ν:ℝ):ℝ:=
  ((assignments (m:=m+1) (List.finRange r)).map
    (fun cs=>|factor (d:=d) P lo hi age cs j0 A0 ν|)).sum

theorem total_nonneg (P:CanonicalCovariance.ProfileParameters) (lo hi:Fin r→ℝ) (age:Fin m→ℝ)
    (j0:Fin m) (A0 ν:ℝ):0≤total (d:=d) P lo hi age j0 A0 ν:=by
  apply List.sum_nonneg
  intro x hx
  obtain ⟨cs,_,rfl⟩:=List.mem_map.mp hx
  exact abs_nonneg _

theorem factor_le_total (P:CanonicalCovariance.ProfileParameters) (lo hi:Fin r→ℝ) (age:Fin m→ℝ)
    (cs:List (Fin r×Fin (m+1))) (j0:Fin m) (A0 ν:ℝ)
    (hc:cs∈assignments (m:=m+1) (List.finRange r)):
    |factor (d:=d) P lo hi age cs j0 A0 ν|≤total (d:=d) P lo hi age j0 A0 ν:=by
  apply List.single_le_sum
  · intro x hx
    obtain ⟨c,_,rfl⟩:=List.mem_map.mp hx
    exact abs_nonneg _
  · exact List.mem_map.mpr ⟨cs,hc,rfl⟩

theorem restore_factor (P:CanonicalCovariance.ProfileParameters) (lo hi:Fin r→ℝ) (age:Fin m→ℝ)
    (cs:List (Fin r×Fin (m+1))) (j0:Fin m) (A0 ν:ℝ) (hb:block cs j0.succ=[]):
    factor (d:=d) P lo hi age cs j0 A0 ν*
      NativeAssignedLeafMoments.leafScale P cs j0.succ lo hi (age j0)
        (MinimumGapChoice.blockChoice lo hi cs j0.succ)=
      MixedPastWordMoments.factor (d:=d) P lo hi age cs A0 ν:=by
  simp only [factor,hb,ite_true,MixedPastWordMoments.factor]
  rw [mul_assoc,Finset.prod_erase_mul Finset.univ _ (Finset.mem_univ j0)]

/-- The omitted baseline retains its ORIGINAL leaf age and all original
assignment gains. The remaining quarter-power is the PAST age q,
not the remaining fresh gap. No Holder constant is divided out. -/
theorem restore_total (P:CanonicalCovariance.ProfileParameters) (dir:CircleL2)
    (lo hi:Fin r→ℝ) (age:Fin m→ℝ) (j0:Fin m) (A0 ν:ℝ)
    {q:ℝ} (hq:0<q) (ha:q≤age j0):
    ControlledScoreRates.sharpConstant P dir*(age j0)^((P.exponent-1)/4)*
      total (d:=d) P lo hi age j0 A0 ν≤
      BaselineOriginalGain.unitSharp P dir*q^(-(1/4:ℝ))*
        MixedPastWordMoments.total (d:=d) P lo hi age A0 ν:=by
  unfold total MixedPastWordMoments.total
  rw [←List.sum_map_mul_left,←List.sum_map_mul_left]
  apply List.sum_le_sum
  intro cs hc
  by_cases hb:block cs j0.succ=[]
  · let s:=NativeAssignedLeafMoments.leafScale P cs j0.succ lo hi (age j0)
      (MinimumGapChoice.blockChoice lo hi cs j0.succ)
    have hs:0≤s:=by
      simp only [s,NativeAssignedLeafMoments.leafScale,dite_eq_left hb]
      exact mul_nonneg P.holder_nonneg (rpow_nonneg (hq.le.trans ha) _)
    have hg:=BaselineOriginalGain.empty_leaf_gain P dir cs j0.succ hb lo hi
      (MinimumGapChoice.blockChoice lo hi cs j0.succ) hq ha
    have hr:|factor (d:=d) P lo hi age cs j0 A0 ν| * s=
        |MixedPastWordMoments.factor (d:=d) P lo hi age cs A0 ν|:=by
      rw [←abs_of_nonneg hs,←abs_mul]
      exact congrArg abs (restore_factor P lo hi age cs j0 A0 ν hb)
    have hh:=mul_le_mul_of_nonneg_right hg (abs_nonneg (factor (d:=d) P lo hi age cs j0 A0 ν))
    rw [←hr]
    convert! hh using 1 <;> ring
  · simp only [factor,hb,ite_false,abs_zero,mul_zero]
    exact mul_nonneg (mul_nonneg (BaselineOriginalGain.unitSharp_nonneg P dir) (rpow_nonneg hq.le _))
      (abs_nonneg _)

end SHE.NativeOmittedTimeTotal
