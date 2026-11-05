module

public import SHE.QuarterBudgetScaling

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false

namespace SHE.QuarterRMSTimeFactors
open Set MeasureTheory Real PhysicalAssignmentGapScale GaussianAssignmentBlocks AssignmentGapPartition
  AllocatedAssignmentKernel CoveredHistoryGeometry
open scoped ENNReal BigOperators
local instance quarterBudgetSquare_finiteExponent : Fact ((2:ℝ≥0∞)≠⊤) := ⟨by simp⟩

theorem assignment_has_gain {k : ℕ} (hk : 0<k) (cs : List (Fin k×Fin (k+1)))
    (hc : cs∈assignments (m:=k+1) (List.finRange k)) : 0<rootCount cs+roughCount cs := by
  classical
  let i : Fin k := ⟨0,hk⟩
  obtain ⟨j,hj⟩ := exists_label cs hc i
  have hm : i∈block cs j := List.mem_filterMap.mpr ⟨(i,j),hj,by simp⟩
  have hn : block cs j≠[] := by intro hz;simpa only [hz,List.not_mem_nil] using hm
  by_cases hj0 : j=0
  · have hp : 0<rootCount cs := by
      simpa only [rootCount,hj0] using List.length_pos_iff.mpr hn
    omega
  · have hp : 0<roughCount cs := Finset.card_pos.mpr ⟨j,by simp [hj0,hn]⟩
    omega

def squareKernel (β ν : ℝ) (a b : ℕ) (w : ℝ) : ℝ :=
  w^(β*(b:ℝ)/4-1/2)*rootMass ν w^a

/-- Genuine current-time square integrability at every nonempty
root/rough assignment. The all-root corner uses the retained root mass,
not a logarithmic supremum. -/
theorem squareKernel_memLp {β ν T : ℝ} (hβ : 0<β) (hν : 0<ν) (hT : 0<T)
    (a b : ℕ) (hab : 0<a+b) :
    MemLp (squareKernel β ν a b) 2 (volume.restrict (Ioc 0 T)) := by
  have hd : 0<β*(b:ℝ)/2+((2*a:ℕ):ℝ)/4 := by
    by_cases hb : b=0
    · have ha : 0<a := by omega
      simp only [hb,Nat.cast_zero,mul_zero,zero_div,zero_add]
      positivity
    · have hb' : (0:ℝ)<b := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hb)
      positivity
  have hi : Integrable (fun w : ℝ => w^(β*(b:ℝ)/2-1)*rootMass ν w^(2*a))
      (volume.restrict (Ioc 0 T)) := (weighted_root_integrable hν hT.le hd).1
  have hm : Measurable (squareKernel β ν a b) :=
    (real_rpow_measurable _).mul ((rootMass_measurable ν).pow_const a)
  apply (memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).mpr
  apply hi.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with w hw
  have hn : 0≤squareKernel β ν a b w :=
    mul_nonneg (Real.rpow_nonneg hw.1.le _) (pow_nonneg (rootMass_nonneg hν.le hw.1.le) _)
  rw [Real.norm_of_nonneg hn]
  unfold squareKernel
  rw [mul_pow,←Real.rpow_mul_natCast hw.1.le,←pow_mul,Nat.mul_comm a 2]
  congr 2
  ring

/-- The full finite old-time budget has a true current-time L2 kernel
at every positive word depth. Depth zero remains a separate leading
term, as required by the endpoint singularity. -/
theorem halfBudget_memLp (Q : CanonicalCovariance.ProfileParameters) (ell : ℝ) (Cs : ℕ→ℝ)
    (k : ℕ) (hk : 0<k) (T A0 ν : ℝ) (hT : 0<T) (hν : 0<ν) :
    MemLp (fun w => oldTimeBudget Q ell Cs k T (T-w) (1/2:ℝ) A0 ν) 2
      (volume.restrict (Ioc 0 T)) := by
  let cs := assignments (m:=k+1) (List.finRange k)
  let v := ν*sqrt (ProfileVariance.upperConstant*(Q.lower/2))
  let K := fun i : Fin cs.length =>
    (scorePrefactor ell Cs k*prefactor Q (cs.get i) A0 1*T^((Q.exponent/4)*(emptyCount (cs.get i):ℝ)))*
      (((k+1:ℕ):ℝ)^2/(1/2:ℝ)*inverseDegreeProduct (cs.get i) (List.get_mem cs i) (Q.exponent/4))
  have hv : 0<v := mul_pos hν (Real.sqrt_pos.mpr (mul_pos ProfileVariance.upperConstant_pos
    (div_pos Q.lower_pos (by norm_num))))
  have hp (i : Fin cs.length) : MemLp
      (fun w => K i*squareKernel Q.exponent v (rootCount (cs.get i)) (roughCount (cs.get i)) w)
      2 (volume.restrict (Ioc 0 T)) :=
    (squareKernel_memLp Q.exponent_pos hv hT _ _ (assignment_has_gain hk _ (List.get_mem cs i))).const_mul _
  have hs := memLp_finsetSum Finset.univ (fun i _ => hp i)
  have heq : (fun w => oldTimeBudget Q ell Cs k T (T-w) (1/2:ℝ) A0 ν)=
      fun w => ∑ i : Fin cs.length,K i*squareKernel Q.exponent v (rootCount (cs.get i)) (roughCount (cs.get i)) w := by
    funext w
    dsimp only [oldTimeBudget]
    apply Finset.sum_congr rfl
    intro i _
    simp only [show T-(T-w)=w by ring]
    dsimp only [K,squareKernel,v,cs]
    rw [show (1/2:ℝ)+(Q.exponent/4)*(roughCount ((assignments (List.finRange k)).get i):ℝ)-1=
      Q.exponent*(roughCount ((assignments (List.finRange k)).get i):ℝ)/4-1/2 by ring]
    ring
  rw [heq]
  exact hs

end SHE.QuarterRMSTimeFactors
