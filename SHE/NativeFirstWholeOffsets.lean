module

public import SHE.NativeFirstWholeMoments
public import SHE.FullResidualOffsetAffine
public import SHE.VaryingFullResidualMoments
public import SHE.PastEventWeights

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1200000
noncomputable section

namespace SHE.NativeFirstWholeMoments
open Set MeasureTheory Real GaussianAssignmentBlocks
open scoped BigOperators
variable {Ω : Type*} [MeasurableSpace Ω] {r m : ℕ}

/-- The complete score/root/rough word constant is affine in the
normalized current offset budget. No product of uncontrolled stochastic
offset moments is introduced when Gaussian covariances vary with the past. -/
theorem constant_affine (P : CanonicalCovariance.ProfileParameters) (b : ℕ)
    (choices : List (Fin r×Fin (m+1))) (C0 : ℝ) :
    constant P r m choices b C0=constant P r m choices b 0+FullResidualAssignedMoments.offsetSlope b choices*C0 := by
  unfold constant FullResidualAssignedMoments.offsetSlope
  simp_rw [OffsetAssignedLeafMoments.leafConstant_affine P (b*(m+2)) C0]
  rw [Finset.sum_add_distrib,←Finset.sum_mul]
  ring

theorem constant_budget_integrable (μ : Measure Ω) (P : CanonicalCovariance.ProfileParameters)
    (b : ℕ) (choices : List (Fin r×Fin (m+1))) (C0 : Ω→ℝ) (hi : Integrable C0 μ) [IsFiniteMeasure μ] :
    Integrable (fun ω=>constant P r m choices b (C0 ω)) μ := by
  have he : (fun ω=>constant P r m choices b (C0 ω)) =
      (fun ω=>constant P r m choices b 0+FullResidualAssignedMoments.offsetSlope b choices*C0 ω) :=
    funext (fun ω=>constant_affine P b choices (C0 ω))
  rw [he]
  exact (integrable_const _).add (hi.const_mul _)

/-- Conditional event offset bounds transfer linearly to the true
varying-data Gaussian word constant, preserving the exact event mass. -/
theorem integral_constant_budget_le (μ : Measure Ω) [IsFiniteMeasure μ]
    (P : CanonicalCovariance.ProfileParameters) (b : ℕ) (choices : List (Fin r×Fin (m+1)))
    (C0 : Ω→ℝ) (hi : Integrable C0 μ) (Cbar : ℝ)
    (hb : (∫ ω,C0 ω ∂μ)≤Cbar*μ.real Set.univ) :
    (∫ ω,constant P r m choices b (C0 ω) ∂μ)≤constant P r m choices b Cbar*μ.real Set.univ := by
  have he : (fun ω=>constant P r m choices b (C0 ω)) =
      (fun ω=>constant P r m choices b 0+FullResidualAssignedMoments.offsetSlope b choices*C0 ω) :=
    funext (fun ω=>constant_affine P b choices (C0 ω))
  rw [he,constant_affine P b choices Cbar]
  rw [integral_add (integrable_const _) (hi.const_mul _),integral_const_mul,integral_const]
  simp only [smul_eq_mul]
  have hh := add_le_add_left (mul_le_mul_of_nonneg_left hb (FullResidualAssignedMoments.offsetSlope_nonneg b choices))
    (μ.real Set.univ*constant P r m choices b 0)
  convert! hh using 1 <;> ring

end SHE.NativeFirstWholeMoments

namespace SHE.NativeFirstWholeMoments
open Set MeasureTheory Real
open scoped BigOperators
variable {Ω : Type*} {m0 past : MeasurableSpace Ω} {r m : ℕ}

theorem constant_nonneg (P:CanonicalCovariance.ProfileParameters) (b:ℕ)
    (choices:List (Fin r×Fin (m+1))) {C:ℝ} (hC:0≤C):0≤constant P r m choices b C:=by
  unfold constant
  exact add_nonneg (add_nonneg
    (mul_nonneg (pow_nonneg (GaussianAudit.secondScoreMoment_nonneg _) _) (GaussianDependentScores.productMomentConstant_nonneg _))
    (ControlledAssignedRoot.constant_nonneg _ _ _))
    (Finset.sum_nonneg (fun j _=>OffsetAssignedLeafMoments.leafConstant_nonneg P _ hC choices j.succ))

/-- The actual affine Gaussian-word constant can be averaged against any
nonnegative past-measurable weight. The later native offsets may depend
on that past in an arbitrary way; bounds on every past event suffice. -/
theorem weighted_offset_constant (μ : @Measure Ω m0) [IsFiniteMeasure μ]
    (hpast : past≤m0) (P : CanonicalCovariance.ProfileParameters) (b : ℕ)
    (choices : List (Fin r×Fin (m+1))) (age : Fin m→ℝ) (hage : ∀ j,0<age j)
    (offset : Ω→Fin m→ℝ) (hoffset : Measurable[m0] offset) (power degree C : ℝ)
    (hC : 0≤C)
    (hmoment : ∀ A,MeasurableSet[past] A→∀ j,
      Integrable (fun ω=>|offset ω j|^power) (μ.restrict A) ∧
      (∫ ω in A,|offset ω j|^power ∂μ)≤C*(age j)^degree*μ.real A)
    (weight : Ω→ℝ) (hw : Measurable[past] weight) (hw0 : ∀ ω,0≤weight ω)
    (hwi : Integrable weight μ) :
    let budget := fun ω=>NormalizedLeafOffsets.budget age (offset ω) power degree
    Integrable (fun ω=>weight ω*constant P r m choices b (budget ω)) μ ∧
      (∫ ω,weight ω*constant P r m choices b (budget ω) ∂μ)≤
        constant P r m choices b ((m:ℝ)*C)*(∫ ω,weight ω ∂μ) := by
  letI : MeasurableSpace Ω := m0
  intro budget
  have hbudget : Measurable budget := NormalizedLeafOffsets.budget_measurable age offset hoffset _ _
  have hbudget0 (ω : Ω) : 0≤budget ω :=
    NormalizedLeafOffsets.budget_nonneg age (offset ω) power degree hage
  have hf : Measurable (fun ω=>constant P r m choices b (budget ω)) := by
    have he : (fun ω=>constant P r m choices b (budget ω))=
        (fun ω=>constant P r m choices b 0+FullResidualAssignedMoments.offsetSlope b choices*budget ω) :=
      funext (fun ω=>constant_affine P b choices (budget ω))
    rw [he]
    exact measurable_const.add (measurable_const.mul hbudget)
  have hbudgetI (A : Set Ω) (hA : MeasurableSet[past] A) : Integrable budget (μ.restrict A) :=
    NormalizedLeafOffsets.budget_integrable (μ.restrict A) age offset power degree
      (fun j=>(hmoment A hA j).1)
  have hbound (A : Set Ω) (hA : MeasurableSet[past] A) :
      (∫ ω in A,constant P r m choices b (budget ω) ∂μ)≤
        constant P r m choices b ((m:ℝ)*C)*μ.real A := by
    have hh := NormalizedLeafOffsets.integral_budget_le (μ.restrict A) age hage offset power degree C
      (fun j=>(hmoment A hA j).1)
      (fun j=>by simpa only [measureReal_restrict_apply_univ] using (hmoment A hA j).2)
    have hc := integral_constant_budget_le (μ.restrict A) P b choices budget (hbudgetI A hA)
      ((m:ℝ)*C) hh
    simpa only [measureReal_restrict_apply_univ] using hc
  have hfi : Integrable (fun ω=>constant P r m choices b (budget ω)) μ := by
    have hh := constant_budget_integrable (μ.restrict univ) P b choices budget
      (hbudgetI univ MeasurableSet.univ)
    simpa only [Measure.restrict_univ] using hh
  exact PastEventWeights.weighted_integral μ hpast _ hf hfi
    (fun ω=>constant_nonneg P b choices (hbudget0 ω))
    (constant P r m choices b ((m:ℝ)*C))
    (constant_nonneg P b choices (mul_nonneg (Nat.cast_nonneg _) hC))
    hbound weight hw hw0 hwi

end SHE.NativeFirstWholeMoments
