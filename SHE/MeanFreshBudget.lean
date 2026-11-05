module

public import SHE.MeanBudgetSquare

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false

namespace SHE.MeanRMSTimeFactors
open Set MeasureTheory Real PhysicalAssignmentGapScale GaussianAssignmentBlocks AssignmentGapPartition
  AllocatedAssignmentKernel CoveredHistoryGeometry QuarterRMSTimeFactors PredictableL2
open scoped ENNReal NNReal BigOperators
local instance meanFreshBudget_finiteExponent : Fact ((2:ℝ≥0∞)≠⊤) := ⟨by simp⟩

def assignmentCoefficient (Q : CanonicalCovariance.ProfileParameters) (ell : ℝ) (Cs : ℕ→ℝ)
    (k : ℕ) (T fresh A0 : ℝ)
    (i : Fin (assignments (m:=k+1) (List.finRange k)).length) : ℝ :=
  let cs := assignments (m:=k+1) (List.finRange k)
  (scorePrefactor ell Cs k*PhysicalAssignmentGapScale.prefactor Q (cs.get i) A0 1*
    T^((Q.exponent/4)*(emptyCount (cs.get i):ℝ)))*
    (((k+1:ℕ):ℝ)^2/fresh*inverseDegreeProduct (cs.get i) (List.get_mem cs i) (Q.exponent/4))

theorem budget_sum_identity (Q : CanonicalCovariance.ProfileParameters) (ell : ℝ) (Cs : ℕ→ℝ)
    (k : ℕ) (ρ T fresh A0 ν : ℝ) {w : ℝ} (hw : 0<w) :
    w^(ρ/2)*oldTimeBudget Q ell Cs k T (T-w) fresh A0 ν=
      ∑ i : Fin (assignments (m:=k+1) (List.finRange k)).length,
        assignmentCoefficient Q ell Cs k T fresh A0 i*
          squareKernel (ρ+2*fresh-1) Q.exponent
            (ν*sqrt (ProfileVariance.upperConstant*(Q.lower/2)))
            (rootCount ((assignments (m:=k+1) (List.finRange k)).get i))
            (roughCount ((assignments (m:=k+1) (List.finRange k)).get i)) w := by
  rw [oldTimeBudget,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp only [show T-(T-w)=w by ring]
  dsimp only [assignmentCoefficient,squareKernel]
  rw [show (ρ+2*fresh-1)/2+Q.exponent*
      (roughCount ((assignments (m:=k+1) (List.finRange k)).get i):ℝ)/4-1/2=
      ρ/2+(fresh+(Q.exponent/4)*(roughCount ((assignments (m:=k+1) (List.finRange k)).get i):ℝ)-1) by ring,
    Real.rpow_add hw]
  ring

/-- The precise integrability margin after trading some retained
exponential damping for a fractional fresh-gap loss. -/
theorem fresh_budget_memLp (Q : CanonicalCovariance.ProfileParameters) (ell : ℝ) (Cs : ℕ→ℝ)
    (k : ℕ) (ρ T fresh A0 ν : ℝ) (hdegree : 0<ρ+2*fresh-1) (hT : 0<T) (hν : 0≤ν) :
    MemLp (fun w => w^(ρ/2)*oldTimeBudget Q ell Cs k T (T-w) fresh A0 ν) 2
      (volume.restrict (Ioc 0 T)) := by
  let cs := assignments (m:=k+1) (List.finRange k)
  let v := ν*sqrt (ProfileVariance.upperConstant*(Q.lower/2))
  have hv : 0≤v := mul_nonneg hν (sqrt_nonneg _)
  have hp (i : Fin cs.length) : MemLp
      (fun w=>assignmentCoefficient Q ell Cs k T fresh A0 i*
        squareKernel (ρ+2*fresh-1) Q.exponent v (rootCount (cs.get i)) (roughCount (cs.get i)) w)
      2 (volume.restrict (Ioc 0 T)) :=
    (squareKernel_memLp hdegree Q.exponent_pos.le hv hT _ _).const_mul _
  have hs := memLp_finsetSum Finset.univ (fun i _=>hp i)
  apply hs.ae_eq
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with w hw
  exact (budget_sum_identity Q ell Cs k ρ T fresh A0 ν hw.1).symm

/-- Changing the fresh degree is an exact power identity for the
literal assignment budget, including its degree denominator. -/
theorem budget_fresh_scale (Q : CanonicalCovariance.ProfileParameters) (ell : ℝ) (Cs : ℕ→ℝ)
    (k : ℕ) (ρ T fresh A0 ν : ℝ) (hfresh : fresh≠0) {w : ℝ} (hw : 0<w) :
    w^(ρ/2)*oldTimeBudget Q ell Cs k T (T-w) fresh A0 ν=
      (1/(2*fresh))*(w^((ρ+2*fresh-1)/2)*oldTimeBudget Q ell Cs k T (T-w) (1/2:ℝ) A0 ν) := by
  rw [budget_sum_identity Q ell Cs k ρ T fresh A0 ν hw,
    budget_sum_identity Q ell Cs k (ρ+2*fresh-1) T (1/2:ℝ) A0 ν hw,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  have he : ρ+2*fresh-1+2*(1/2:ℝ)-1=ρ+2*fresh-1 := by ring
  rw [he]
  dsimp only [assignmentCoefficient]
  field_simp
  <;> ring

theorem squareKernel_integral_bound {ρ β ν T : ℝ} (hρ : 0<ρ) (hβ : 0≤β)
    (hν : 0≤ν) (hT : 0<T) (a b : ℕ) :
    Integrable (fun w=>squareKernel ρ β ν a b w^2) (volume.restrict (Ioc 0 T)) ∧
      (∫ w,squareKernel ρ β ν a b w^2 ∂volume.restrict (Ioc 0 T))≤
        T^(ρ+β*(b:ℝ)/2)/(ρ+β*(b:ℝ)/2)*rootMass ν T^(2*a) := by
  have hd : 0<ρ+β*(b:ℝ)/2 := by positivity
  have hm : Measurable (squareKernel ρ β ν a b) :=
    (real_rpow_measurable _).mul ((rootMass_measurable ν).pow_const a)
  have hi := (memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).mp
    (squareKernel_memLp hρ hβ hν hT a b)
  have hi' : Integrable (fun w=>squareKernel ρ β ν a b w^2) (volume.restrict (Ioc 0 T)) := by
    simpa only [Real.norm_eq_abs,sq_abs] using hi
  refine ⟨hi',?_⟩
  have he : (fun w=>squareKernel ρ β ν a b w^2)=ᵐ[volume.restrict (Ioc 0 T)]
      (fun w=>w^(ρ+β*(b:ℝ)/2-1)*rootMass ν w^(2*a)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with w hw
    unfold squareKernel
    rw [mul_pow,←Real.rpow_mul_natCast hw.1.le,←pow_mul,Nat.mul_comm a 2]
    congr 2
    ring
  rw [integral_congr_ae he,←intervalIntegral.integral_of_le hT.le]
  exact weighted_root_mass_pos_le hν hd hT.le (2*a)

/-- An explicit finite assignment bound for the full current-time
square. Every actual root count, rough count and empty-leaf gain is
retained, so frequency limits can be taken after fixing the depth. -/
theorem fresh_budget_square_bound (Q : CanonicalCovariance.ProfileParameters) (ell : ℝ) (Cs : ℕ→ℝ)
    (k : ℕ) (ρ T fresh A0 ν : ℝ) (hdegree : 0<ρ+2*fresh-1) (hT : 0<T) (hν : 0≤ν) :
    let cs := assignments (m:=k+1) (List.finRange k)
    let v := ν*sqrt (ProfileVariance.upperConstant*(Q.lower/2))
    let degree := fun i : Fin cs.length=>ρ+2*fresh-1+Q.exponent*(roughCount (cs.get i):ℝ)/2
    (∫ w,(w^(ρ/2)*oldTimeBudget Q ell Cs k T (T-w) fresh A0 ν)^2
      ∂volume.restrict (Ioc 0 T))≤
      (cs.length:ℝ)*∑ i : Fin cs.length,(assignmentCoefficient Q ell Cs k T fresh A0 i)^2*
        (T^(degree i)/(degree i)*rootMass v T^(2*rootCount (cs.get i))) := by
  intro cs v degree
  let f := fun i : Fin cs.length=>fun w=>assignmentCoefficient Q ell Cs k T fresh A0 i*
    squareKernel (ρ+2*fresh-1) Q.exponent v (rootCount (cs.get i)) (roughCount (cs.get i)) w
  have hv : 0≤v := mul_nonneg hν (sqrt_nonneg _)
  have hp (i : Fin cs.length) := squareKernel_integral_bound hdegree Q.exponent_pos.le hv hT
    (rootCount (cs.get i)) (roughCount (cs.get i))
  have hi (i : Fin cs.length) : Integrable (fun w=>f i w^2) (volume.restrict (Ioc 0 T)) := by
    simpa only [f,mul_pow] using (hp i).1.const_mul ((assignmentCoefficient Q ell Cs k T fresh A0 i)^2)
  have hm : Measurable (fun w=>w^(ρ/2)*oldTimeBudget Q ell Cs k T (T-w) fresh A0 ν) :=
    (measurable_id.pow_const _).mul
      ((oldTimeBudget_measurable Q ell Cs k T fresh A0 ν).comp (measurable_const.sub measurable_id))
  have hi0 := (memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).mp
    (fresh_budget_memLp Q ell Cs k ρ T fresh A0 ν hdegree hT hν)
  have hs := integrable_finsetSum Finset.univ (fun i _=>hi i)
  have hb : ∀ᵐ w ∂volume.restrict (Ioc 0 T),
      (w^(ρ/2)*oldTimeBudget Q ell Cs k T (T-w) fresh A0 ν)^2≤(cs.length:ℝ)*∑ i,f i w^2 := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with w hw
    rw [budget_sum_identity Q ell Cs k ρ T fresh A0 ν hw.1]
    simpa only [f,one_mul,one_pow,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one]
      using Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun _ : Fin cs.length=>(1:ℝ)) (fun i=>f i w)
  have hmain := integral_mono_ae (by simpa only [Real.norm_eq_abs,sq_abs] using hi0)
    (hs.const_mul (cs.length:ℝ)) hb
  rw [integral_const_mul,integral_finsetSum _ (fun i _=>hi i)] at hmain
  refine hmain.trans (mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i _=>?_)) (Nat.cast_nonneg _))
  change (∫ w,(assignmentCoefficient Q ell Cs k T fresh A0 i*squareKernel (ρ+2*fresh-1) Q.exponent v
      (rootCount (cs.get i)) (roughCount (cs.get i)) w)^2 ∂volume.restrict (Ioc 0 T))≤_
  simp_rw [mul_pow]
  rw [integral_const_mul]
  exact mul_le_mul_of_nonneg_left (hp i).2 (sq_nonneg _)

end SHE.MeanRMSTimeFactors
