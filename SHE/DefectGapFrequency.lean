module
public import SHE.DefectGapMixture
public import SHE.MeanAssignmentFrequency
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
namespace SHE.DefectGapFrequency
open Set MeasureTheory Real GaussianAssignmentBlocks AllocatedAssignmentKernel
  PhysicalAssignmentGapScale DefectGapDensity
open scoped BigOperators
open Classical

def epsilon (k:ℕ)(η:ℝ):ℝ:=η/(4*((k+1:ℕ):ℝ))
def rootConstant (P:CanonicalCovariance.ProfileParameters)(k:ℕ)(η:ℝ):ℝ:=
  (4+1/epsilon k η)*(1+sqrt (ProfileVariance.upperConstant*(P.lower/2)))^(4*epsilon k η)
def constant (P:CanonicalCovariance.ProfileParameters)(ell:ℝ)(C:ℕ→ℝ)(k:ℕ)(A0 η:ℝ):ℝ:=
  scorePrefactor ell C k*∑i:Fin (count k),
    BoundedEmptyAssignmentTime.prefactor P (choices k i) A0 1*
      (((k+1:ℕ):ℝ)^2*inverseDegreeProduct (choices k i) (choices_mem k i) (P.exponent/4))*
        rootConstant P k η^(rootCount (choices k i))

theorem constant_nonneg (P:CanonicalCovariance.ProfileParameters){ell A0 η:ℝ}
    (hell:0<ell)(C:ℕ→ℝ)(hC:∀j,0≤C j)(k:ℕ)(hA0:0≤A0)(hη:0<η):
    0≤constant P ell C k A0 η:=by
  have hε:0<epsilon k η:=by unfold epsilon;positivity
  have hK:0≤rootConstant P k η:=by unfold rootConstant;positivity
  apply mul_nonneg (scorePrefactor_nonneg hell C hC k)
  apply Finset.sum_nonneg
  intro i _
  have hi:=inverseDegreeProduct_nonneg (choices k i) (choices_mem k i)
    (a:=P.exponent/4) (by have :=P.exponent_pos;positivity)
      (by have :=P.exponent_le_one;linarith)
  exact mul_nonneg (mul_nonneg (BoundedEmptyAssignmentTime.prefactor_nonneg P _ hA0 1)
    (mul_nonneg (sq_nonneg _) hi)) (pow_nonneg hK _)

/-- Every fixed-depth full old-history mass has arbitrarily small
root-frequency loss, uniformly over all physical spans in [0,1]. -/
theorem mass_le (P:CanonicalCovariance.ProfileParameters){ell A0 η h ν:ℝ}
    (hell:0<ell)(C:ℕ→ℝ)(hC:∀j,0≤C j)(k:ℕ)(hA0:0≤A0)(hη:0<η)
    (hh:0≤h)(hh1:h≤1)(hν:0≤ν):
    mass P ell C k h A0 ν≤constant P ell C k A0 η*(1+ν)^η:=by
  let ε:=epsilon k η
  let K:=rootConstant P k η
  let c:=sqrt (ProfileVariance.upperConstant*(P.lower/2))
  have hε:0<ε:=by dsimp [ε,epsilon];positivity
  have hK:0≤K:=by dsimp [K,rootConstant];positivity
  have hroot:rootMass (ν*c) h≤K*(1+ν)^(4*ε):=
    rootMass_scaled_frequency_bound hν (sqrt_nonneg _) hh hh1 hε
  have hp(i:Fin (count k)):rootMass (ν*c) h^(rootCount (choices k i))≤
      K^(rootCount (choices k i))*(1+ν)^η:=by
    have hr:=pow_le_pow_left₀ (rootMass_nonneg (mul_nonneg hν (sqrt_nonneg _)) hh)
      hroot (rootCount (choices k i))
    rw [mul_pow,←rpow_mul_natCast (show 0≤1+ν by positivity)] at hr
    have hc:=PastMeanTimeFactors.assignment_rootCount_le (choices k i) (choices_mem k i)
    have hcount:((rootCount (choices k i):ℕ):ℝ)≤((k+1:ℕ):ℝ):=by
      exact_mod_cast hc.trans (Nat.le_succ k)
    have he:4*ε*((k+1:ℕ):ℝ)=η:=by dsimp [ε,epsilon];field_simp
    have hexp:4*ε*((rootCount (choices k i):ℕ):ℝ)≤η:=
      (mul_le_mul_of_nonneg_left hcount (by positivity:0≤4*ε)).trans_eq he
    exact hr.trans (mul_le_mul_of_nonneg_left
      (rpow_le_rpow_of_exponent_le (show 1≤1+ν by linarith) hexp) (pow_nonneg hK _))
  unfold mass constant
  rw [mul_assoc,Finset.sum_mul]
  apply mul_le_mul_of_nonneg_left _ (scorePrefactor_nonneg hell C hC k)
  apply Finset.sum_le_sum
  intro i _
  have hi:=inverseDegreeProduct_nonneg (choices k i) (choices_mem k i)
    (a:=P.exponent/4) (by have :=P.exponent_pos;positivity)
      (by have :=P.exponent_le_one;linarith)
  have ha:0≤(P.exponent/4)*(roughCount (choices k i):ℝ):=
    mul_nonneg (by have :=P.exponent_pos;positivity) (Nat.cast_nonneg _)
  have hspan:h^((P.exponent/4)*(roughCount (choices k i):ℝ))≤1:=
    rpow_le_one hh hh1 ha
  have hcoef:0≤((k+1:ℕ):ℝ)^2*inverseDegreeProduct (choices k i) (choices_mem k i) (P.exponent/4):=
    mul_nonneg (sq_nonneg _) hi
  have hleft:=mul_le_mul_of_nonneg_right hspan
    (pow_nonneg (rootMass_nonneg (mul_nonneg hν (show 0≤c from sqrt_nonneg _)) hh)
      (rootCount (choices k i)))
  rw [one_mul] at hleft
  have hb:=(hleft.trans (hp i))
  have hc:=mul_le_mul_of_nonneg_left hb
    (mul_nonneg (BoundedEmptyAssignmentTime.prefactor_nonneg P (choices k i) hA0 1) hcoef)
  convert! hc using 1 <;> dsimp only [c,K] <;> ring

theorem constant_amplitude (P:CanonicalCovariance.ProfileParameters)(ell:ℝ)(C:ℕ→ℝ)
    (k:ℕ)(A0 η:ℝ):constant P ell C k A0 η=A0*constant P ell C k 1 η:=by
  unfold constant
  have hp(i:Fin (count k)):BoundedEmptyAssignmentTime.prefactor P (choices k i) A0 1=
      A0*BoundedEmptyAssignmentTime.prefactor P (choices k i) 1 1:=by
    unfold BoundedEmptyAssignmentTime.prefactor
    ring
  simp_rw [hp,mul_assoc]
  rw [←Finset.mul_sum]
  ring
end SHE.DefectGapFrequency
