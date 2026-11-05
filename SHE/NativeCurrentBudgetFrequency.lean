module

public import SHE.NativeCurrentRootFrequency
public import SHE.FiniteMomentSum

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
noncomputable section

namespace SHE.NativeCurrentBudgetFrequency
open Set MeasureTheory Real GaussianAssignmentBlocks AssignmentGapPartition AllocatedAssignmentKernel
  MeanRMSTimeFactors QuarterRMSTimeFactors PhysicalAssignmentGapScale
open scoped BigOperators
open Classical

/-- A positive reflected time kernel independent of the actual window.
Every genuine assignment root count and rough-block count is retained. -/
def majorant (P:CanonicalCovariance.ProfileParameters)(ell:ℝ)(Cs:ℕ→ℝ)
    (k:ℕ)(ρ χ ν w:ℝ):ℝ:=
  ∑i:Fin (assignments (m:=k+1) (List.finRange k)).length,
    |assignmentCoefficient P ell Cs k 1 ((2-χ)/4) 1 i| * 
      |squareKernel (ρ-χ/2) P.exponent (ν*Real.sqrt (ProfileVariance.upperConstant*(P.lower/2)))
        (rootCount ((assignments (m:=k+1) (List.finRange k)).get i))
        (roughCount ((assignments (m:=k+1) (List.finRange k)).get i)) w|

theorem majorant_nonneg (P:CanonicalCovariance.ProfileParameters)(ell:ℝ)(Cs:ℕ→ℝ)
    (k:ℕ)(ρ χ ν w:ℝ):0≤majorant P ell Cs k ρ χ ν w:=
  Finset.sum_nonneg (fun _ _=>mul_nonneg (abs_nonneg _) (abs_nonneg _))

theorem majorant_measurable (P:CanonicalCovariance.ProfileParameters)(ell:ℝ)(Cs:ℕ→ℝ)
    (k:ℕ)(ρ χ ν:ℝ):Measurable (majorant P ell Cs k ρ χ ν):=by
  apply Finset.measurable_sum
  intro i _
  exact measurable_const.mul (continuous_abs.measurable.comp
    ((real_rpow_measurable _).mul ((rootMass_measurable _).pow_const _)))

/-- Exact root amplitude and full empty-leaf age homogeneity. -/
theorem coefficient_factor (P:CanonicalCovariance.ProfileParameters)(ell:ℝ)(Cs:ℕ→ℝ)
    (k:ℕ)(T fresh A0:ℝ)(i:Fin (assignments (m:=k+1) (List.finRange k)).length):
    assignmentCoefficient P ell Cs k T fresh A0 i=
      A0*T^((P.exponent/4)*(emptyCount ((assignments (m:=k+1) (List.finRange k)).get i):ℝ))*
        assignmentCoefficient P ell Cs k 1 fresh 1 i:=by
  simp only [assignmentCoefficient,PhysicalAssignmentGapScale.prefactor,one_rpow,mul_one]
  ring

/-- The literal old-time budget for every window T<=1 is dominated by
one fixed reflected kernel. This supports both moving complete windows
and the initial triangular output region, with no displacement supremum. -/
theorem budget_le (P:CanonicalCovariance.ProfileParameters)(ell:ℝ)(Cs:ℕ→ℝ)
    (k:ℕ)(ρ χ ν T A0:ℝ)(hT:0<T)(hT1:T≤1){w:ℝ}(hw:0<w):
    |w^(ρ/2)*oldTimeBudget P ell Cs k T (T-w) ((2-χ)/4) A0 ν|≤
      |A0| * majorant P ell Cs k ρ χ ν w:=by
  rw [budget_sum_identity P ell Cs k ρ T ((2-χ)/4) A0 ν hw]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  rw [majorant,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  have he:ρ+2*((2-χ)/4)-1=ρ-χ/2:=by ring
  rw [he,abs_mul,coefficient_factor,abs_mul,abs_mul,
    abs_of_nonneg (Real.rpow_nonneg hT.le _)]
  have hexp:0≤(P.exponent/4)*(emptyCount ((assignments (m:=k+1) (List.finRange k)).get i):ℝ):=
    mul_nonneg (div_nonneg P.exponent_pos.le (by norm_num)) (Nat.cast_nonneg _)
  have hpow:T^((P.exponent/4)*(emptyCount ((assignments (m:=k+1) (List.finRange k)).get i):ℝ))≤1:=
    Real.rpow_le_one hT.le hT1 hexp
  have hh:=mul_le_mul_of_nonneg_left hpow (abs_nonneg A0)
  have hh':|A0| * T^((P.exponent/4)*(emptyCount ((assignments (m:=k+1) (List.finRange k)).get i):ℝ))≤|A0|:=by
    simpa only [mul_one] using hh
  convert! mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hh' (abs_nonneg _)) (abs_nonneg _) using 1 <;> ring

/-- The full finite-assignment reflected kernel has a uniform L2
frequency bound BEFORE the actual band time window is chosen. -/
theorem majorant_energy (P:CanonicalCovariance.ProfileParameters)(ell:ℝ)(Cs:ℕ→ℝ)
    (k:ℕ)(hk:0<k)(ρ χ:ℝ)(hρ:0<ρ)(hχ:χ<1)(hmargin:χ<P.exponent+2*ρ)
    (η:ℝ)(hη:0<η):
    ∃C:ℝ,0<C ∧ ∀ν T:ℝ,0<ν→0<T→T≤1→
      Integrable (fun w=>majorant P ell Cs k ρ χ ν w^2) (volume.restrict (Ioc 0 T)) ∧
      (∫w,majorant P ell Cs k ρ χ ν w^2 ∂volume.restrict (Ioc 0 T))≤
        C*(1+ν)^(max 0 (2*χ-4*ρ)+η):=by
  let cs:=assignments (m:=k+1) (List.finRange k)
  let c:=Real.sqrt (ProfileVariance.upperConstant*(P.lower/2))
  let D:=max 0 (2*χ-4*ρ)+η
  have hc:0<c:=Real.sqrt_pos.mpr (mul_pos ProfileVariance.upperConstant_pos (by linarith [P.lower_pos]))
  have hD:0≤D:=by dsimp only [D];have := le_max_left 0 (2*χ-4*ρ);linarith
  choose C hCpos hCb using (fun i:Fin cs.length=>
    NativeCurrentRootFrequency.assignment_bound (cs.get i) (List.get_mem cs i) hk hρ hχ P.exponent_pos hmargin hη)
  let B:ℝ:=(cs.length:ℝ)*∑i:Fin cs.length,
    (assignmentCoefficient P ell Cs k 1 ((2-χ)/4) 1 i)^2*C i*(1+c)^D
  have hB:0≤B:=by
    apply mul_nonneg (Nat.cast_nonneg _)
    exact Finset.sum_nonneg (fun i _=>mul_nonneg (mul_nonneg (sq_nonneg _) (hCpos i).le)
      (Real.rpow_nonneg (by positivity) _))
  refine ⟨1+B,by linarith,?_⟩
  intro ν T hν hT hT1
  let f:=fun i:Fin cs.length=>fun w=>|assignmentCoefficient P ell Cs k 1 ((2-χ)/4) 1 i| * 
    |squareKernel (ρ-χ/2) P.exponent (ν*c) (rootCount (cs.get i)) (roughCount (cs.get i)) w|
  have hi(i:Fin cs.length):Integrable (fun w=>f i w^2) (volume.restrict (Ioc 0 T)):=by
    have hs:=NativeCurrentSquareCorners.assignment_integrable (cs.get i) (List.get_mem cs i) hk
      hρ hχ P.exponent_pos hmargin (mul_pos hν hc) hT.le
    simpa only [f,mul_pow,sq_abs] using hs.const_mul
      ((assignmentCoefficient P ell Cs k 1 ((2-χ)/4) 1 i)^2)
  have hm(i:Fin cs.length):Measurable (f i):=measurable_const.mul
    (continuous_abs.measurable.comp ((real_rpow_measurable _).mul ((rootMass_measurable _).pow_const _)))
  have hfi(i:Fin cs.length):MemLp (f i) 2 (volume.restrict (Ioc 0 T)):=
    (memLp_two_iff_integrable_sq (hm i).aestronglyMeasurable).mpr (hi i)
  have hsum:MemLp (majorant P ell Cs k ρ χ ν) 2 (volume.restrict (Ioc 0 T)):=
    memLp_finsetSum Finset.univ (fun i _=>hfi i)
  have hpow:(1+ν*c)^D≤(1+c)^D*(1+ν)^D:=by
    have hh:=Real.rpow_le_rpow (by positivity : 0≤1+ν*c)
      (show 1+ν*c≤(1+c)*(1+ν) by nlinarith) hD
    rwa [Real.mul_rpow (by positivity : 0≤1+c) (by positivity : 0≤1+ν)] at hh
  have hfiBound(i:Fin cs.length):(∫w,f i w^2 ∂volume.restrict (Ioc 0 T))≤
      (assignmentCoefficient P ell Cs k 1 ((2-χ)/4) 1 i)^2*C i*(1+c)^D*(1+ν)^D:=by
    have hh:=(hCb i (ν*c) T (mul_pos hν hc) hT hT1).trans
      (mul_le_mul_of_nonneg_left hpow (hCpos i).le)
    simp_rw [f,mul_pow,sq_abs,integral_const_mul]
    convert! mul_le_mul_of_nonneg_left hh
      (sq_nonneg (assignmentCoefficient P ell Cs k 1 ((2-χ)/4) 1 i)) using 1 <;> ring
  have hb:∀w,(majorant P ell Cs k ρ χ ν w)^2≤(cs.length:ℝ)*∑i:Fin cs.length,f i w^2:=by
    intro w
    change (∑i:Fin cs.length,f i w)^2≤_
    simpa only [Fintype.card_fin,show 2-1=1 from rfl,pow_one] using
      FiniteMomentSum.sum_pow_le 2 (by norm_num) (fun i:Fin cs.length=>f i w)
        (fun i=>mul_nonneg (abs_nonneg _) (abs_nonneg _))
  refine ⟨hsum.integrable_sq,?_⟩
  have hh:=integral_mono hsum.integrable_sq
    ((integrable_finsetSum Finset.univ (fun i _=>hi i)).const_mul (cs.length:ℝ)) hb
  rw [integral_const_mul,integral_finsetSum _ (fun i _=>hi i)] at hh
  apply (hh.trans (mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i _=>hfiBound i))
    (Nat.cast_nonneg _))).trans
  have he:(cs.length:ℝ)*∑i:Fin cs.length,
      (assignmentCoefficient P ell Cs k 1 ((2-χ)/4) 1 i)^2*C i*(1+c)^D*(1+ν)^D=B*(1+ν)^D:=by
    dsimp only [B]
    simp only [Finset.mul_sum,Finset.sum_mul,mul_assoc]
  rw [he]
  exact mul_le_mul_of_nonneg_right (by linarith : B≤1+B) (Real.rpow_nonneg (by positivity) _)

end SHE.NativeCurrentBudgetFrequency
