module
public import SHE.DefectGapDensity
public import SHE.BoundedEmptyAssignmentTime
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
namespace SHE.DefectGapDensityMass
open Set MeasureTheory Real GaussianAssignmentBlocks AllocatedAssignmentKernel OrderedGapCoordinates
  PhysicalAssignmentGapScale DefectGapDensity
open scoped NNReal ENNReal BigOperators
open Classical

/-- The COMPLETE old-history collision density is integrable with the
actual finite assignment/rootMass bound. No positive collision cutoff
or empty-leaf current-age gain is introduced. -/
theorem integral (P:CanonicalCovariance.ProfileParameters){ell h A0 ν:ℝ}(hell:0<ell)(hh:0<h)
    (C:ℕ→ℝ)(hC:∀j,0≤C j)(k:ℕ)(hA0:0≤A0)(hν:0≤ν):
    Integrable (density P ell C k h A0 ν) ∧
      (∫d:Fin k→ℝ,density P ell C k h A0 ν d)≤mass P ell C k h A0 ν:=by
  let V:=ν*sqrt (ProfileVariance.upperConstant*(P.lower/2))
  have hV:0≤V:=mul_nonneg hν (sqrt_nonneg _)
  let I:Fin (count k)→(Fin k→ℝ)→ℝ:=fun i d=>
    if (∀j,0<d j) ∧ (∑j,d j)<h then weight (choices k i) V (P.exponent/4) d else 0
  have hi(i:Fin (count k)):Integrable (I i):=by
    have hb:=BoundedEmptyAssignmentTime.ordered_weight_integral P (choices k i) (choices_mem k i)
      (q:=0) (T:=h) hV hh
    have hg:=(ordered_integrable_iff 0 h k (weight (choices k i) V (P.exponent/4))).mp hb.1
    simpa only [sub_zero] using hg
  have hb(i:Fin (count k)):(∫d:Fin k→ℝ,I i d)≤
      ((((k+1:ℕ):ℝ)^2*inverseDegreeProduct (choices k i) (choices_mem k i) (P.exponent/4))*
        h^((P.exponent/4)*(roughCount (choices k i):ℝ))*rootMass V h^(rootCount (choices k i))):=by
    have hg:= (BoundedEmptyAssignmentTime.ordered_weight_integral P (choices k i) (choices_mem k i)
      (q:=0) (T:=h) hV hh).2
    rw [ordered_integral] at hg
    simpa only [sub_zero] using hg
  have he:density P ell C k h A0 ν=fun d:Fin k→ℝ=>
      scorePrefactor ell C k*(∑i:Fin (count k),BoundedEmptyAssignmentTime.prefactor P (choices k i) A0 1*I i d):=by
    funext d
    by_cases hd:(∀j,0<d j) ∧ (∑j,d j)<h
    · simp only [density,if_pos hd,raw,I,if_pos hd,V]
    · simp only [density,if_neg hd,I,if_neg hd,mul_zero,Finset.sum_const_zero]
  have hs:Integrable (fun d:Fin k→ℝ=>∑i:Fin (count k),BoundedEmptyAssignmentTime.prefactor P (choices k i) A0 1*I i d):=
    integrable_finsetSum _ (fun i _=>(hi i).const_mul _)
  refine ⟨he ▸ hs.const_mul _,?_⟩
  rw [he,integral_const_mul,integral_finsetSum _ (fun i _=>(hi i).const_mul _)]
  apply mul_le_mul_of_nonneg_left _ (scorePrefactor_nonneg hell C hC k)
  apply Finset.sum_le_sum
  intro i _
  rw [integral_const_mul]
  exact mul_le_mul_of_nonneg_left (hb i) (BoundedEmptyAssignmentTime.prefactor_nonneg P _ hA0 1)

end SHE.DefectGapDensityMass
