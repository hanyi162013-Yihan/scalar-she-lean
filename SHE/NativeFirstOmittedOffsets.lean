module

public import SHE.NativeFirstOmittedMoments
public import SHE.FullResidualOffsetAffine
public import SHE.PastEventWeights

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1600000
noncomputable section

namespace SHE.NativeFirstOmittedMoments
open Set MeasureTheory Real
open scoped BigOperators
variable {Ω : Type*} {m0 past : MeasurableSpace Ω} {r m : ℕ}

def offsetSlope (b : ℕ) (choices : List (Fin r×Fin (m+1))) (j0 : Fin m) : ℝ :=
  ∑ j : Fin m,if j=j0 then 0 else if GaussianAssignmentBlocks.block choices j.succ=[]
    then (2:ℝ)^(2*(b*(m+2))-1) else 0

theorem offsetSlope_nonneg (b : ℕ) (choices : List (Fin r×Fin (m+1))) (j0 : Fin m) :
    0≤offsetSlope b choices j0 := by
  apply Finset.sum_nonneg
  intro j _
  split_ifs <;> positivity

theorem constant_nonneg (P : CanonicalCovariance.ProfileParameters) (b : ℕ)
    (choices : List (Fin r×Fin (m+1))) (j0 : Fin m) {C0 : ℝ} (hC0 : 0≤C0) :
    0≤constant P r m choices j0 b C0 := by
  unfold constant
  apply add_nonneg (add_nonneg (mul_nonneg (pow_nonneg (GaussianAudit.secondScoreMoment_nonneg _) _) (GaussianDependentScores.productMomentConstant_nonneg _))
    (ControlledAssignedRoot.constant_nonneg _ _ _))
  apply Finset.sum_nonneg
  intro j _
  split_ifs
  · positivity
  · exact OffsetAssignedLeafMoments.leafConstant_nonneg P _ hC0 choices j.succ

/-- Only surviving unassigned leaves contribute native current offsets.
The removed leaf contributes exactly no offset slope. -/
theorem constant_affine (P : CanonicalCovariance.ProfileParameters) (b : ℕ)
    (choices : List (Fin r×Fin (m+1))) (j0 : Fin m) (C0 : ℝ) :
    constant P r m choices j0 b C0=constant P r m choices j0 b 0+offsetSlope b choices j0*C0 := by
  classical
  have he (j : Fin m) :
      (if j=j0 then (1:ℝ) else OffsetAssignedLeafMoments.leafConstant P (b*(m+2)) C0 choices j.succ)=
      (if j=j0 then (1:ℝ) else OffsetAssignedLeafMoments.leafConstant P (b*(m+2)) 0 choices j.succ)+
      (if j=j0 then 0 else if GaussianAssignmentBlocks.block choices j.succ=[]
        then (2:ℝ)^(2*(b*(m+2))-1) else 0)*C0 := by
    by_cases hj : j=j0
    · simp only [ite_eq_left hj,zero_mul,add_zero]
    · simp only [ite_eq_right hj,OffsetAssignedLeafMoments.leafConstant_affine P (b*(m+2)) C0]
  unfold constant offsetSlope
  simp_rw [he]
  rw [Finset.sum_add_distrib,←Finset.sum_mul]
  ring

theorem constant_budget_integrable (μ : @Measure Ω m0) [IsFiniteMeasure μ]
    (P : CanonicalCovariance.ProfileParameters) (b : ℕ)
    (choices : List (Fin r×Fin (m+1))) (j0 : Fin m) (budget : Ω→ℝ) (hi : Integrable budget μ) :
    Integrable (fun ω=>constant P r m choices j0 b (budget ω)) μ := by
  have he : (fun ω=>constant P r m choices j0 b (budget ω))=
      (fun ω=>constant P r m choices j0 b 0+offsetSlope b choices j0*budget ω) :=
    funext (fun ω=>constant_affine P b choices j0 (budget ω))
  rw [he]
  exact (integrable_const _).add (hi.const_mul _)

theorem integral_constant_budget_le (μ : @Measure Ω m0) [IsFiniteMeasure μ]
    (P : CanonicalCovariance.ProfileParameters) (b : ℕ)
    (choices : List (Fin r×Fin (m+1))) (j0 : Fin m) (budget : Ω→ℝ) (hi : Integrable budget μ)
    (Cbar : ℝ) (hb : (∫ ω,budget ω ∂μ)≤Cbar*μ.real univ) :
    (∫ ω,constant P r m choices j0 b (budget ω) ∂μ)≤constant P r m choices j0 b Cbar*μ.real univ := by
  have he : (fun ω=>constant P r m choices j0 b (budget ω))=
      (fun ω=>constant P r m choices j0 b 0+offsetSlope b choices j0*budget ω) :=
    funext (fun ω=>constant_affine P b choices j0 (budget ω))
  rw [he,constant_affine P b choices j0 Cbar]
  rw [integral_add (integrable_const _) (hi.const_mul _),integral_const_mul,integral_const]
  simp only [smul_eq_mul]
  have hh:=add_le_add_left (mul_le_mul_of_nonneg_left hb (offsetSlope_nonneg b choices j0))
    (μ.real univ*constant P r m choices j0 b 0)
  convert! hh using 1 <;> ring

/-- Actual conditional native offset bounds can be integrated against
any past-measurable weight after the baseline leaf has been removed. -/
theorem weighted_offset_constant (μ : @Measure Ω m0) [IsFiniteMeasure μ]
    (hpast : past≤m0) (P : CanonicalCovariance.ProfileParameters) (b : ℕ)
    (choices : List (Fin r×Fin (m+1))) (j0 : Fin m) (age : Fin m→ℝ) (hage : ∀ j,0<age j)
    (offset : Ω→Fin m→ℝ) (hoffset : Measurable[m0] offset) (power degree C : ℝ)
    (hC : 0≤C)
    (hmoment : ∀ A,MeasurableSet[past] A→∀ j,
      Integrable (fun ω=>|offset ω j|^power) (μ.restrict A) ∧
      (∫ ω in A,|offset ω j|^power ∂μ)≤C*(age j)^degree*μ.real A)
    (weight : Ω→ℝ) (hw : Measurable[past] weight) (hw0 : ∀ ω,0≤weight ω)
    (hwi : Integrable weight μ) :
    let budget := fun ω=>NormalizedLeafOffsets.budget age (offset ω) power degree
    Integrable (fun ω=>weight ω*constant P r m choices j0 b (budget ω)) μ ∧
      (∫ ω,weight ω*constant P r m choices j0 b (budget ω) ∂μ)≤
        constant P r m choices j0 b ((m:ℝ)*C)*(∫ ω,weight ω ∂μ) := by
  letI : MeasurableSpace Ω:=m0
  intro budget
  have hbudget : Measurable budget:=NormalizedLeafOffsets.budget_measurable age offset hoffset _ _
  have hbudget0 (ω:Ω) : 0≤budget ω:=NormalizedLeafOffsets.budget_nonneg age (offset ω) power degree hage
  have hf : Measurable (fun ω=>constant P r m choices j0 b (budget ω)) := by
    have he : (fun ω=>constant P r m choices j0 b (budget ω))=
        (fun ω=>constant P r m choices j0 b 0+offsetSlope b choices j0*budget ω) :=
      funext (fun ω=>constant_affine P b choices j0 (budget ω))
    rw [he]
    exact measurable_const.add (measurable_const.mul hbudget)
  have hi (A:Set Ω) (hA:MeasurableSet[past] A) : Integrable budget (μ.restrict A):=
    NormalizedLeafOffsets.budget_integrable _ _ _ _ _ (fun j=>(hmoment A hA j).1)
  have hb (A:Set Ω) (hA:MeasurableSet[past] A) :
      (∫ ω in A,constant P r m choices j0 b (budget ω) ∂μ)≤
        constant P r m choices j0 b ((m:ℝ)*C)*μ.real A := by
    have hh:=NormalizedLeafOffsets.integral_budget_le (μ.restrict A) age hage offset power degree C
      (fun j=>(hmoment A hA j).1)
      (fun j=>by simpa only [measureReal_restrict_apply_univ] using (hmoment A hA j).2)
    simpa only [measureReal_restrict_apply_univ] using
      integral_constant_budget_le (μ.restrict A) P b choices j0 budget (hi A hA) ((m:ℝ)*C) hh
  have hfi : Integrable (fun ω=>constant P r m choices j0 b (budget ω)) μ := by
    simpa only [Measure.restrict_univ] using
      constant_budget_integrable (μ.restrict univ) P b choices j0 budget (hi univ MeasurableSet.univ)
  exact PastEventWeights.weighted_integral μ hpast _ hf hfi
    (fun ω=>constant_nonneg P b choices j0 (hbudget0 ω))
    (constant P r m choices j0 b ((m:ℝ)*C))
    (constant_nonneg P b choices j0 (mul_nonneg (Nat.cast_nonneg _) hC)) hb weight hw hw0 hwi

end SHE.NativeFirstOmittedMoments

