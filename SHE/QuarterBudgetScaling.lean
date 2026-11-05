module

public import SHE.QuarterRMSOldTime

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false

namespace SHE.QuarterRMSTimeFactors
open Set MeasureTheory Real RawTraceTimeEnvelope PhysicalAssignmentGapScale GaussianAssignmentBlocks
  AllocatedAssignmentKernel CoveredHistoryGeometry
open scoped BigOperators

private theorem scaled_term {w f g : ℝ} (hw : 0<w) (hf : 0<f) (hg : 0<g) (K a : ℝ) :
    w^(g-f)*(K/f*w^(f+a-1))=g/f*(K/g*w^(g+a-1)) := by
  have hp : w^(g-f)*w^(f+a-1)=w^(g+a-1) := by
    rw [←Real.rpow_add hw]
    congr 1
    ring
  calc
    _ = (K/f)*(w^(g-f)*w^(f+a-1)) := by ring
    _ = (K/f)*w^(g+a-1) := by rw [hp]
    _ = _ := by field_simp [hf.ne',hg.ne']

/-- Changing only the fresh degree changes the actual finite assignment
budget by one exact power and the exact reciprocal degree factor. -/
theorem oldTimeBudget_scaling (Q : CanonicalCovariance.ProfileParameters) (ell : ℝ)
    (Cs : ℕ→ℝ) (k : ℕ) (T q f g A0 ν : ℝ) (hw : q<T) (hf : 0<f) (hg : 0<g) :
    (T-q)^(g-f)*oldTimeBudget Q ell Cs k T q f A0 ν=
      (g/f)*oldTimeBudget Q ell Cs k T q g A0 ν := by
  dsimp only [oldTimeBudget]
  rw [Finset.mul_sum,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  let cs := GaussianAssignmentBlocks.assignments (m:=k+1) (List.finRange k)
  let a := (Q.exponent/4)*(roughCount (cs.get i):ℝ)
  let K := (scorePrefactor ell Cs k*prefactor Q (cs.get i) A0 1*
      T^((Q.exponent/4)*(emptyCount (cs.get i):ℝ)))*
      (((k+1:ℕ):ℝ)^2*inverseDegreeProduct (cs.get i) (List.get_mem cs i) (Q.exponent/4))*
      rootMass (ν*sqrt (ProfileVariance.upperConstant*(Q.lower/2))) (T-q)^(rootCount (cs.get i))
  convert! scaled_term (sub_pos.mpr hw) hf hg K a using 1 <;> dsimp only [K,a,cs] <;> ring

theorem goodTimeFactor_width (J ρ η cutoff : ℝ) (k : ℕ) (Cf ell w : ℝ) :
    goodTimeFactor J ρ η cutoff k Cf ell w=
      goodTimeFactor J ρ η cutoff k Cf ell 1*w^((ρ+η)/2) := by
  unfold goodTimeFactor goodAmplitude
  simp only [one_rpow]
  ring

/-- At the native root target A=T the outside Sobolev/output power
cancels the fresh loss exactly, before the actual current-time square.
Every root mass and rough/empty-leaf factor is retained. -/
theorem good_old_budget_cancel (Q : CanonicalCovariance.ProfileParameters) (ell : ℝ)
    (Cs : ℕ→ℝ) (k : ℕ) (T q A0 ν J ρ η cutoff Cf : ℝ)
    (hw : q<T) (hρη : ρ+η<1) :
    goodTimeFactor J ρ η cutoff k Cf ell (T-q)*
      oldTimeBudget Q ell Cs k T q (freshDegree ρ η) A0 ν=
      (goodTimeFactor J ρ η cutoff k Cf ell 1/(2*freshDegree ρ η))*
        oldTimeBudget Q ell Cs k T q (1/2:ℝ) A0 ν := by
  have hf := freshDegree_pos hρη
  have he : (1/2:ℝ)-freshDegree ρ η=(ρ+η)/2 := by
    unfold freshDegree freshExponent
    ring
  rw [goodTimeFactor_width]
  rw [mul_assoc,←he,oldTimeBudget_scaling Q ell Cs k T q _ (1/2:ℝ) A0 ν hw hf (by norm_num)]
  field_simp [hf.ne']

end SHE.QuarterRMSTimeFactors
