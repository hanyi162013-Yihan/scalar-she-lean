module

public import SHE.DefectGapOffsets
public import SHE.DefectRelativeFactor
public import SHE.PhysicalAssignmentTimeFactors

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000

namespace SHE.DefectGapDensity
open Set MeasureTheory Real GaussianAssignmentBlocks AllocatedAssignmentKernel OrderedGapCoordinates
  CutoffWordLevel CutoffWordHistories CutoffCarriers PhysicalChainArrays PhysicalParentGeometry PhysicalScoreChain
  CoveredControlledLaw CoveredHistoryGeometry PhysicalAssignmentGapScale HistoryProductMeasure
open scoped BigOperators
open Classical
local instance defectGapDensity_period:Fact (0<2*Real.pi):=⟨by positivity⟩

def count(k:ℕ):ℕ:=(assignments (m:=k+1) (List.finRange k)).length
def choices(k:ℕ)(i:Fin (count k)):List (Fin k×Fin (k+1)):=
  (assignments (m:=k+1) (List.finRange k)).get i
theorem choices_mem(k:ℕ)(i:Fin (count k)):
    choices k i∈assignments (m:=k+1) (List.finRange k):=List.get_mem _ _

def raw (P:CanonicalCovariance.ProfileParameters)(ell:ℝ)(C:ℕ→ℝ)(k:ℕ)(A0 ν:ℝ)(d:Fin k→ℝ):ℝ:=
  scorePrefactor ell C k*∑i:Fin (count k),
    BoundedEmptyAssignmentTime.prefactor P (choices k i) A0 1*
      weight (choices k i) (ν*sqrt (ProfileVariance.upperConstant*(P.lower/2))) (P.exponent/4) d

def density (P:CanonicalCovariance.ProfileParameters)(ell:ℝ)(C:ℕ→ℝ)(k:ℕ)(h A0 ν:ℝ)
    (d:Fin k→ℝ):ℝ:=
  if (∀i,0<d i) ∧ (∑i,d i)<h then raw P ell C k A0 ν d else 0

def mass (P:CanonicalCovariance.ProfileParameters)(ell:ℝ)(C:ℕ→ℝ)(k:ℕ)(h A0 ν:ℝ):ℝ:=
  scorePrefactor ell C k*∑i:Fin (count k),
    BoundedEmptyAssignmentTime.prefactor P (choices k i) A0 1*
      ((((k+1:ℕ):ℝ)^2*inverseDegreeProduct (choices k i) (choices_mem k i) (P.exponent/4))*
        h^((P.exponent/4)*(roughCount (choices k i):ℝ))*
          rootMass (ν*sqrt (ProfileVariance.upperConstant*(P.lower/2))) h^(rootCount (choices k i)))

theorem weight_measurable {k:ℕ}(cs:List (Fin k×Fin (k+1)))(ν a:ℝ):
    Measurable (weight cs ν a):=by
  unfold weight
  apply Finset.measurable_prod
  intro l _
  unfold blockWeight
  by_cases hl:l=0
  · simp only [hl,ite_true,rootKernel]
    apply Finset.measurable_prod
    intro j _
    exact ((measurable_pi_apply _).pow_const _).mul
      (measurable_const.min (measurable_const.mul ((measurable_pi_apply _).pow_const _)))
  · simp only [hl,ite_false]
    split_ifs with hb
    · exact measurable_const
    · exact (Finset.measurable_prod (Finset.univ:Finset (Fin (block cs l).length))
        (fun j _=>(measurable_pi_apply ((block cs l).get j)).inv)).mul
        ((MinimumGapChoice.choose_value_measurable (fun d:Fin k→ℝ=>d)
          (fun i=>measurable_pi_apply i) _ hb).pow_const _)

theorem density_measurable (P:CanonicalCovariance.ProfileParameters)(ell:ℝ)(C:ℕ→ℝ)
    (k:ℕ)(h A0 ν:ℝ):Measurable (density P ell C k h A0 ν):=by
  have hr:Measurable (raw P ell C k A0 ν):=
    measurable_const.mul (Finset.measurable_sum _ (fun i _=>measurable_const.mul (weight_measurable _ _ _)))
  exact hr.ite (simplex_measurableSet k h) measurable_const

theorem raw_nonneg (P:CanonicalCovariance.ProfileParameters){ell:ℝ}(hell:0<ell)
    (C:ℕ→ℝ)(hC:∀j,0≤C j)(k:ℕ){A0 ν:ℝ}(hA0:0≤A0)(hν:0≤ν)
    (d:Fin k→ℝ)(hd:∀i,0<d i):0≤raw P ell C k A0 ν d:=by
  apply mul_nonneg (scorePrefactor_nonneg hell C hC k)
  apply Finset.sum_nonneg
  intro i _
  exact mul_nonneg (BoundedEmptyAssignmentTime.prefactor_nonneg P _ hA0 1)
    (Finset.prod_nonneg (fun l _=>blockWeight_nonneg _ (mul_nonneg hν (sqrt_nonneg _)) d hd l))

theorem density_nonneg (P:CanonicalCovariance.ProfileParameters){ell:ℝ}(hell:0<ell)
    (C:ℕ→ℝ)(hC:∀j,0≤C j)(k:ℕ){h A0 ν:ℝ}(hA0:0≤A0)(hν:0≤ν):
    ∀d,0≤density P ell C k h A0 ν d:=by
  intro d
  unfold density
  split_ifs with hd
  · exact raw_nonneg P hell C hC k hA0 hν d hd.1
  · exact le_rfl

variable {R:ReferenceData}{X:Type}[MeasurableSpace X](L:Level R X 1)

/-- The original physical old denominator and bounded-empty word sum
are EXACTLY a function of the original positive gaps. -/
theorem actual (P:CanonicalCovariance.ProfileParameters)(ell:ℝ)(C:ℕ→ℝ)(v:ℝ)
    (T:ℝ)(hT:∀x,L.terminal x=T)(k:ℕ)(t:Fin k→ℝ)(x:X)(w:Fin k→StoppedFourier.HeatCircle)
    (hp:StrictHistory L k (separated k (x,t,w))){A0 ν:ℝ}(hA0:0≤A0)(hν:0≤ν):
    timeWeight L ell C k (separated k (x,t,w))*
      TwoFreshBoundedEmptyWord.total (d:=1) P
        (fun j=>lower L k (separated k (x,t,w)) j-v)
        (fun j=>upper L k (separated k (x,t,w)) j-v) (fun _:Fin k=>0) A0 ν=
      raw P ell C k A0 ν (gaps T k t):=by
  let p:=separated k (x,t,w)
  let lo:=fun j=>lower L k p j-v
  let hi:=fun j=>upper L k p j-v
  have hd(j:Fin k):lo j<hi j:=sub_lt_sub_right (lower_lt_upper L k p hp j) v
  have hgap:(fun j=>hi j-lo j)=gaps T k t:=by
    convert PhysicalOrderedGaps.old_gaps_eq L T hT k t x w hp using 1
    funext j
    dsimp [lo,hi]
    ring
  have htotal:TwoFreshBoundedEmptyWord.total (d:=1) P lo hi (fun _:Fin k=>0) A0 ν=
      ∑i:Fin (count k),|TwoFreshBoundedEmptyWord.factor (d:=1) P lo hi (fun _:Fin k=>0)
        (choices k i) A0 ν|:=by
    symm
    simpa only [choices,count,TwoFreshBoundedEmptyWord.total,List.get_eq_getElem] using
      Fin.sum_univ_fun_getElem (assignments (m:=k+1) (List.finRange k))
        (fun cs=>|TwoFreshBoundedEmptyWord.factor (d:=1) P lo hi (fun _:Fin k=>0) cs A0 ν|)
  change timeWeight L ell C k p*TwoFreshBoundedEmptyWord.total (d:=1) P lo hi (fun _:Fin k=>0) A0 ν=_
  rw [htotal,PhysicalAssignmentGapScale.timeWeight_eq,Finset.mul_sum]
  unfold raw
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  have hh:=BoundedEmptyAssignmentTime.inverse_factor_eq_weight P lo hi (fun _:Fin k=>0)
    (choices k i) (choices_mem k i) hA0 hν 1 hd
  have hgapj(j:Fin k):hi j-lo j=gaps T k t j:=congrFun hgap j
  simp_rw [hgapj] at hh
  try rw [hgap] at hh
  have he:(∏j,(upper L k p j-lower L k p j)⁻¹)=∏j,(gaps T k t j)⁻¹:=by
    apply Finset.prod_congr rfl
    intro j _
    exact congrArg Inv.inv (congrFun (PhysicalOrderedGaps.old_gaps_eq L T hT k t x w hp) j)
  rw [he,mul_assoc]
  exact congrArg (fun a:ℝ=>scorePrefactor ell C k*a) hh

end SHE.DefectGapDensity
