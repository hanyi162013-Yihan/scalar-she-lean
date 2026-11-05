module

public import SHE.TwoFreshBoundedEmptyWord
public import SHE.PhysicalAssignmentGapScale

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2300000

namespace SHE.BoundedEmptyAssignmentTime
open Set MeasureTheory Real GaussianAssignmentBlocks AllocatedAssignmentKernel
open scoped BigOperators
open Classical
variable {k:ℕ}

def leafPrefactor (P:CanonicalCovariance.ProfileParameters)(cs:List (Fin k×Fin (k+1)))(j:Fin k):ℝ:=
  if block cs j.succ=[] then 2*P.upper else PhysicalAssignmentGapScale.leafPrefactor P cs j

def prefactor (P:CanonicalCovariance.ProfileParameters)(cs:List (Fin k×Fin (k+1)))
    (A0:ℝ)(n:ℕ):ℝ:=
  (2:ℝ)^(block cs 0).length*A0*(n:ℝ)^(block cs 0).length*∏j,leafPrefactor P cs j

theorem prefactor_nonneg (P:CanonicalCovariance.ProfileParameters)(cs:List (Fin k×Fin (k+1)))
    {A0:ℝ}(hA0:0≤A0)(n:ℕ):0≤prefactor P cs A0 n:=by
  unfold prefactor
  apply mul_nonneg (by positivity)
  apply Finset.prod_nonneg
  intro j _
  unfold leafPrefactor PhysicalAssignmentGapScale.leafPrefactor
  split_ifs
  · exact mul_nonneg (by norm_num) (P.lower_pos.le.trans ((P.lower_bound 0).trans (P.upper_bound 0)))
  · exact mul_nonneg (mul_nonneg (by positivity) P.holder_nonneg)
      (Real.rpow_nonneg (mul_nonneg ProfileVariance.upperConstant_pos.le
        (div_nonneg P.lower_pos.le (by norm_num))) _)

/-- The exact bounded-empty first-defect factor retains all old root
clips and all nonempty rough-block minima. Empty blocks have a fixed
coefficient cap, so no current-state or observation-age moment is used. -/
theorem factor_eq_gain (P:CanonicalCovariance.ProfileParameters)(lo hi:Fin k→ℝ)
    (age:Fin k→ℝ)(cs:List (Fin k×Fin (k+1)))(A0 ν:ℝ)(n:ℕ):
    TwoFreshBoundedEmptyWord.factor (d:=n) P lo hi age cs A0 ν=
      prefactor P cs A0 n*gain cs (ν*sqrt (ProfileVariance.upperConstant*(P.lower/2)))
        (P.exponent/4) (fun i=>hi i-lo i):=by
  have hl(j:Fin k):BoundedEmptyAssignedLeaf.leafScale P cs j.succ lo hi (age j)
      (MinimumGapChoice.blockChoice lo hi cs j.succ)=
      leafPrefactor P cs j*(if h:block cs j.succ=[] then 1 else
        (hi (MinimumGapChoice.choose (fun i=>hi i-lo i) (block cs j.succ) h)-
          lo (MinimumGapChoice.choose (fun i=>hi i-lo i) (block cs j.succ) h))^(P.exponent/4)):=by
    unfold BoundedEmptyAssignedLeaf.leafScale NativeAssignedLeafMoments.leafScale
      leafPrefactor PhysicalAssignmentGapScale.leafPrefactor MinimumGapChoice.blockChoice
    split_ifs <;>simp only [mul_one]
  rw [TwoFreshBoundedEmptyWord.factor]
  simp_rw [hl]
  rw [Finset.prod_mul_distrib,gain_eq_root_rough]
  unfold prefactor VectorPhysicalRoot.scale
  ring

theorem inverse_factor_eq_weight (P:CanonicalCovariance.ProfileParameters)(lo hi:Fin k→ℝ)
    (age:Fin k→ℝ)(cs:List (Fin k×Fin (k+1)))
    (hc:cs∈assignments (m:=k+1) (List.finRange k))
    {A0 ν:ℝ}(hA0:0≤A0)(hν:0≤ν)(n:ℕ)(hd:∀i,lo i<hi i):
    (∏i,(hi i-lo i)⁻¹)*|TwoFreshBoundedEmptyWord.factor (d:=n) P lo hi age cs A0 ν|=
      prefactor P cs A0 n*weight cs (ν*sqrt (ProfileVariance.upperConstant*(P.lower/2)))
        (P.exponent/4) (fun i=>hi i-lo i):=by
  have hg:0≤gain cs (ν*sqrt (ProfileVariance.upperConstant*(P.lower/2)))
      (P.exponent/4) (fun i=>hi i-lo i):=by
    unfold gain
    exact Finset.prod_nonneg (fun l _=>gainBlock_nonneg cs (mul_nonneg hν (sqrt_nonneg _)) _ _
      (fun i=>(sub_pos.mpr (hd i)).le) l)
  rw [factor_eq_gain,abs_of_nonneg (mul_nonneg (prefactor_nonneg P cs hA0 n) hg)]
  rw [mul_left_comm, inverse_mul_gain_eq_weight cs hc]

/-- Integration over the FULL old collision simplex. No positive
recursive time cutoff remains, and each original root mass is retained. -/
theorem ordered_weight_integral (P:CanonicalCovariance.ProfileParameters)
    (cs:List (Fin k×Fin (k+1)))(hc:cs∈assignments (m:=k+1) (List.finRange k))
    {ν q T:ℝ}(hν:0≤ν)(hqT:q<T):
    Integrable (fun t:Fin k→ℝ=>if OrderedGapCoordinates.ordered q T k t then
      weight cs ν (P.exponent/4) (OrderedGapCoordinates.gaps T k t) else 0) ∧
    (∫t:Fin k→ℝ,if OrderedGapCoordinates.ordered q T k t then
      weight cs ν (P.exponent/4) (OrderedGapCoordinates.gaps T k t) else 0)≤
      (((k+1:ℕ):ℝ)^2*inverseDegreeProduct cs hc (P.exponent/4))*
        (T-q)^((P.exponent/4)*(roughCount cs:ℝ))*rootMass ν (T-q)^(rootCount cs):=by
  have hh:=ordered_assignment_integral_bound cs hc hν (by have :=P.exponent_pos;positivity)
    (by have :=P.exponent_le_one;linarith: P.exponent/4≤1) (by norm_num:0<(1:ℝ))
    (le_refl (1:ℝ)) hqT
  norm_num only [sub_self,Real.rpow_zero,one_mul,div_one] at hh
  convert! hh using 1 <;>congr 2 <;>ring

end SHE.BoundedEmptyAssignmentTime
