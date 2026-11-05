module

public import SHE.PairedRoughWordMoments
public import SHE.NoFreshOffsetCalculus

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1400000
noncomputable section

namespace SHE.PairedRoughWordMoments
open Set MeasureTheory Real GaussianAssignmentBlocks OffsetAssignedLeafMoments
open scoped BigOperators
variable {Ω : Type*} [MeasurableSpace Ω] {r m k : ℕ}

def pairSlope (choices : List (Fin r×Fin k)) (factor : Fin k) (p : ℕ) : ℝ :=
  if block choices factor=[] then 2*(2:ℝ)^(2*p-1)*(2:ℝ)^(2*p-1) else 0

theorem pairConstant_affine (P : CanonicalCovariance.ProfileParameters)
    (choices : List (Fin r×Fin k)) (factor : Fin k) (χ : ℝ) (p : ℕ) (C0 : ℝ) :
    pairConstant P choices factor χ p C0=pairConstant P choices factor χ p 0+
      pairSlope choices factor p*C0 := by
  unfold pairConstant pairSlope
  split_ifs with hb
  · simp only [leafConstant_affine P p C0,hb,ite_true]
    ring
  · ring

def offsetSlope (choices : List (Fin r×Fin (m+1))) (j0 : Fin m) (b : ℕ) : ℝ :=
  ∑j:Fin m,if j=j0 then pairSlope choices j0.succ (b*(m+2))
    else if block choices j.succ=[] then (2:ℝ)^(2*(b*(m+2))-1) else 0

theorem offsetSlope_nonneg (choices : List (Fin r×Fin (m+1))) (j0 : Fin m) (b : ℕ) :
    0≤offsetSlope choices j0 b := by
  apply Finset.sum_nonneg
  intro j _
  unfold pairSlope
  split_ifs <;> positivity

theorem constant_nonneg (P:CanonicalCovariance.ProfileParameters)
    (choices:List (Fin r×Fin (m+1))) (j0:Fin m) (χ:ℝ) (b:ℕ) {C0:ℝ} (hC0:0≤C0) :
    0≤constant P choices j0 χ b C0 := by
  unfold constant
  apply add_nonneg (add_nonneg (pow_nonneg (GaussianAudit.secondScoreMoment_nonneg _) _)
    (ControlledAssignedRoot.constant_nonneg _ _ _))
  apply Finset.sum_nonneg
  intro j _
  split_ifs
  · unfold pairConstant
    split_ifs
    · exact add_nonneg (by norm_num) (mul_nonneg (by positivity)
        (add_nonneg (leafConstant_nonneg P _ hC0 choices _) (leafConstant_nonneg P _ hC0 choices _)))
    · exact GaussianAudit.gaussianAbsMoment_nonneg _
  · exact leafConstant_nonneg P _ hC0 choices _

/-- Pairing an EMPTY leaf does not multiply uncontrolled current-offset
moments. The complete dependent word still has an AFFINE offset budget. -/
theorem constant_affine (P : CanonicalCovariance.ProfileParameters)
    (choices : List (Fin r×Fin (m+1))) (j0 : Fin m) (χ : ℝ) (b : ℕ) (C0 : ℝ) :
    constant P choices j0 χ b C0=constant P choices j0 χ b 0+offsetSlope choices j0 b*C0 := by
  unfold constant offsetSlope
  have he (j:Fin m) :
      (if j=j0 then pairConstant P choices j0.succ χ (b*(m+2)) C0
        else leafConstant P (b*(m+2)) C0 choices j.succ)=
      (if j=j0 then pairConstant P choices j0.succ χ (b*(m+2)) 0
        else leafConstant P (b*(m+2)) 0 choices j.succ)+
      (if j=j0 then pairSlope choices j0.succ (b*(m+2))
        else if block choices j.succ=[] then (2:ℝ)^(2*(b*(m+2))-1) else 0)*C0 := by
    by_cases hj:j=j0
    · simp only [hj,ite_true]
      exact pairConstant_affine P choices j0.succ χ (b*(m+2)) C0
    · simp only [hj,ite_false]
      exact leafConstant_affine P (b*(m+2)) C0 choices j.succ
  simp_rw [he]
  rw [Finset.sum_add_distrib,←Finset.sum_mul]
  ring

/-- Genuine integration of the full rough-paired constant against an
arbitrary integrable PAST weight; only the actual weighted offset budget
enters the bound. -/
theorem weighted_constant (μ : Measure Ω) (P : CanonicalCovariance.ProfileParameters)
    (choices : List (Fin r×Fin (m+1))) (j0 : Fin m) (χ : ℝ) (b : ℕ)
    (C0 weight : Ω→ℝ) (hw : Integrable weight μ)
    (hbudget : Integrable (fun ω=>weight ω*C0 ω) μ) (Cbar : ℝ)
    (hb : (∫ω,weight ω*C0 ω ∂μ)≤Cbar*(∫ω,weight ω ∂μ)) :
    Integrable (fun ω=>weight ω*constant P choices j0 χ b (C0 ω)) μ ∧
      (∫ω,weight ω*constant P choices j0 χ b (C0 ω) ∂μ)≤
        constant P choices j0 χ b Cbar*(∫ω,weight ω ∂μ) := by
  have he : (fun ω=>weight ω*constant P choices j0 χ b (C0 ω))=
      (fun ω=>weight ω*constant P choices j0 χ b 0+
        offsetSlope choices j0 b*(weight ω*C0 ω)) := by
    funext ω
    rw [constant_affine]
    ring
  rw [he]
  have hi:Integrable (fun ω=>weight ω*constant P choices j0 χ b 0+
      offsetSlope choices j0 b*(weight ω*C0 ω)) μ :=
    (hw.mul_const (constant P choices j0 χ b 0)).add (hbudget.const_mul (offsetSlope choices j0 b))
  refine ⟨hi,?_⟩
  rw [integral_add (hw.mul_const (constant P choices j0 χ b 0)) (hbudget.const_mul (offsetSlope choices j0 b)),integral_mul_const,integral_const_mul,
    constant_affine P choices j0 χ b Cbar]
  have hh:=mul_le_mul_of_nonneg_left hb (offsetSlope_nonneg choices j0 b)
  nlinarith

end SHE.PairedRoughWordMoments
