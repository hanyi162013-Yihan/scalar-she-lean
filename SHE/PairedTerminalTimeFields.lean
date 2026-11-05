module

public import SHE.PastWordTimeFields
public import SHE.PairedPhysicalGapScale

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1700000
noncomputable section
namespace SHE.PairedTerminalTimeFields
open Set MeasureTheory Real GaussianAssignmentBlocks WordRecursion CutoffWordLevel CutoffWordHistories
  CutoffCarriers PhysicalChainArrays CoveredControlledLaw
open scoped BigOperators
variable {X:Type*} [MeasurableSpace X] {k:ℕ}

def roughFactor (P:CanonicalCovariance.ProfileParameters) (lo hi age:Fin k→ℝ)
    (cs:List (Fin k×Fin (k+1))) (j0:Fin k) (χ A0 ν:ℝ):ℝ:=
  VectorPhysicalRoot.scale cs 0 lo hi A0 ν (P.lower/2) 1*
    ∏j,PairedRoughVaryingMoments.leafScale P cs j0 χ lo hi age (fun j=>j)
      (fun j=>MinimumGapChoice.blockChoice lo hi cs j.succ) j

def factor (P:CanonicalCovariance.ProfileParameters) (lo hi age:Fin k→ℝ)
    (cs:List (Fin k×Fin (k+1))) (χ A0 ν:ℝ) (i:Fin (k+1)):ℝ:=
  Fin.cases (2*MixedPastWordMoments.factor (d:=1) P lo hi age cs A0 ν)
    (fun j=>roughFactor P lo hi age cs j χ A0 ν) i

theorem roughFactor_measurable (P:CanonicalCovariance.ProfileParameters) (lo hi age:X→Fin k→ℝ)
    (hlo:∀j,Measurable (fun x=>lo x j)) (hhi:∀j,Measurable (fun x=>hi x j))
    (hage:∀j,Measurable (fun x=>age x j))
    (cs:List (Fin k×Fin (k+1))) (j0:Fin k) (χ A0 ν:ℝ):
    Measurable (fun x=>roughFactor P (lo x) (hi x) (age x) cs j0 χ A0 ν):=by
  have hr:Measurable (fun x=>VectorPhysicalRoot.scale cs 0 (lo x) (hi x) A0 ν (P.lower/2) 1):=by
    unfold VectorPhysicalRoot.scale
    apply measurable_const.mul
    apply Finset.measurable_prod
    intro j _
    exact measurable_const.min (((hhi _).sub (hlo _)).pow_const (1/4:ℝ) |>.const_mul _)
  have hl(j:Fin k):Measurable (fun x=>PairedRoughVaryingMoments.leafScale P cs j0 χ
      (lo x) (hi x) (age x) (fun j=>j)
      (fun j=>MinimumGapChoice.blockChoice (lo x) (hi x) cs j.succ) j):=by
    unfold PairedRoughVaryingMoments.leafScale
    split_ifs with hj
    · unfold PairedRoughWordMoments.pairScale
      split_ifs with hb
      · exact (measurable_const.mul ((hage j0).pow_const _)).pow_const _
      · exact measurable_const.mul ((MinimumGapChoice.blockChoice_gap_measurable
          lo hi hlo hhi cs j0.succ hb).pow_const _)
    · unfold NativeAssignedLeafMoments.leafScale
      split_ifs with hb
      · exact measurable_const.mul ((hage j).pow_const _)
      · exact measurable_const.mul ((MinimumGapChoice.blockChoice_gap_measurable
          lo hi hlo hhi cs j.succ hb).pow_const _)
  exact hr.mul (Finset.measurable_prod Finset.univ (fun j _=>hl j))

theorem factor_measurable (P:CanonicalCovariance.ProfileParameters) (lo hi age:X→Fin k→ℝ)
    (hlo:∀j,Measurable (fun x=>lo x j)) (hhi:∀j,Measurable (fun x=>hi x j))
    (hage:∀j,Measurable (fun x=>age x j))
    (cs:List (Fin k×Fin (k+1))) (χ A0 ν:ℝ) (i:Fin (k+1)):
    Measurable (fun x=>factor P (lo x) (hi x) (age x) cs χ A0 ν i):=by
  refine Fin.cases ?_ (fun j=>?_) i
  · exact (MixedPastWordMoments.factor_measurable P lo hi age hlo hhi hage cs A0 ν 1).const_mul 2
  · exact roughFactor_measurable P lo hi age hlo hhi hage cs j χ A0 ν

/-- The physical rough-pair factor is exactly the proved heterogeneous
minimum-gap kernel; no degree is hidden in a constant. -/
theorem roughFactor_eq_gaps (P:CanonicalCovariance.ProfileParameters) (lo hi age:Fin k→ℝ)
    (cs:List (Fin k×Fin (k+1))) (j0:Fin k) (χ A0 ν:ℝ):
    roughFactor P lo hi age cs j0 χ A0 ν=
      PairedPhysicalGapScale.factor P cs j0 χ (fun j=>hi j-lo j) age A0 ν:=by
  unfold roughFactor PairedPhysicalGapScale.factor
  congr 1
  · simp only [VectorPhysicalRoot.scale,sub_zero]
  · apply Finset.prod_congr rfl
    intro j _
    unfold PairedRoughVaryingMoments.leafScale
    split_ifs with hj
    · unfold PairedRoughWordMoments.pairScale MinimumGapChoice.blockChoice
      split_ifs <;> simp only [sub_zero]
    · unfold NativeAssignedLeafMoments.leafScale MinimumGapChoice.blockChoice
      split_ifs <;> simp only [sub_zero]

end SHE.PairedTerminalTimeFields
