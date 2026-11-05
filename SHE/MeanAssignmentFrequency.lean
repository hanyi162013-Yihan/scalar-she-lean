module

public import SHE.PastMeanBudgetMass
public import SHE.RootMassFrequency

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
namespace SHE.PastMeanTimeFactors
open Set MeasureTheory Real GaussianAssignmentBlocks AssignmentGapPartition AllocatedAssignmentKernel
open scoped BigOperators

theorem assignment_rootCount_le {k : ℕ} (cs : List (Fin k×Fin (k+1)))
    (hc : cs∈assignments (m:=k+1) (List.finRange k)) : rootCount cs≤k := by
  unfold rootCount
  rw [←block_length cs hc 0]
  exact (Finset.card_filter_le _ _).trans_eq (by simp)

def frequencyEpsilon (k : ℕ) (η : ℝ) : ℝ:=η/(8*((k+1:ℕ):ℝ))

def frequencyRootConstant (P : CanonicalCovariance.ProfileParameters) (k : ℕ) (η : ℝ) : ℝ:=
  (4+1/frequencyEpsilon k η)*
    (1+sqrt (ProfileVariance.upperConstant*(P.lower/2)))^(4*frequencyEpsilon k η)

def assignmentFrequencyConstant (P : CanonicalCovariance.ProfileParameters) (ell : ℝ) (Cs : ℕ→ℝ)
    (k : ℕ) (ρ span fresh A0 η : ℝ) : ℝ :=
  let cs:=assignments (m:=k+1) (List.finRange k)
  let degree:=fun i : Fin cs.length=>ρ+2*fresh-1+P.exponent*(roughCount (cs.get i):ℝ)/2
  (cs.length:ℝ)*∑ i : Fin cs.length,
    (MeanRMSTimeFactors.assignmentCoefficient P ell Cs k span fresh A0 i)^2*
    (span^(degree i)/(degree i)*frequencyRootConstant P k η^(2*rootCount (cs.get i)))

/-- At each FIXED finite depth the exact assignment budget grows
slower than every positive root-frequency power. The horizon is fixed
before the frequency is chosen; no frequency-dependent gap is imposed. -/
theorem assignmentMass_frequency_bound (P : CanonicalCovariance.ProfileParameters) (ell : ℝ) (Cs : ℕ→ℝ)
    (k : ℕ) (ρ span fresh A0 η : ℝ) (hdegree : 0<ρ+2*fresh-1)
    (hspan : 0≤span) (hspan1 : span≤1) (hη : 0<η) {ν : ℝ} (hν : 0≤ν) :
    assignmentMass P ell Cs k ρ span fresh A0 ν≤
      assignmentFrequencyConstant P ell Cs k ρ span fresh A0 η*(1+ν)^η := by
  let cs:=assignments (m:=k+1) (List.finRange k)
  let ε:=frequencyEpsilon k η
  let c:=sqrt (ProfileVariance.upperConstant*(P.lower/2))
  let K:=frequencyRootConstant P k η
  have hε : 0<ε:=by dsimp [ε,frequencyEpsilon];positivity
  have hK : 0≤K:=by dsimp [K,frequencyRootConstant];positivity
  have hroot : rootMass (ν*c) span≤K*(1+ν)^(4*ε):=
    rootMass_scaled_frequency_bound hν (sqrt_nonneg _) hspan hspan1 hε
  have hpow (i : Fin cs.length) : rootMass (ν*c) span^(2*rootCount (cs.get i))≤
      K^(2*rootCount (cs.get i))*(1+ν)^η := by
    have hp:=pow_le_pow_left₀ (rootMass_nonneg (mul_nonneg hν (sqrt_nonneg _)) hspan)
      hroot (2*rootCount (cs.get i))
    rw [mul_pow,←rpow_mul_natCast (show 0≤1+ν by positivity)] at hp
    have hc:=assignment_rootCount_le (cs.get i) (List.get_mem cs i)
    have hcount : (((2*rootCount (cs.get i)):ℕ):ℝ)≤2*((k+1:ℕ):ℝ):=by
      exact_mod_cast Nat.mul_le_mul_left 2 (hc.trans (Nat.le_succ k))
    have hexp : 4*ε*(((2*rootCount (cs.get i)):ℕ):ℝ)≤η:=by
      have hh:=mul_le_mul_of_nonneg_left hcount (show 0≤4*ε by positivity)
      have he : 4*ε*(2*((k+1:ℕ):ℝ))=η:=by
        dsimp [ε,frequencyEpsilon]
        field_simp
        <;> ring
      exact hh.trans_eq he
    exact hp.trans (mul_le_mul_of_nonneg_left
      (rpow_le_rpow_of_exponent_le (show 1≤1+ν by linarith) hexp) (pow_nonneg hK _))
  let degree:=fun i : Fin cs.length=>ρ+2*fresh-1+P.exponent*(roughCount (cs.get i):ℝ)/2
  have hd (i : Fin cs.length) : 0<degree i:=add_pos_of_pos_of_nonneg hdegree
    (div_nonneg (mul_nonneg P.exponent_pos.le (Nat.cast_nonneg _)) (by norm_num))
  unfold assignmentMass assignmentFrequencyConstant
  change (cs.length:ℝ)*∑ i : Fin cs.length,
      (MeanRMSTimeFactors.assignmentCoefficient P ell Cs k span fresh A0 i)^2*
        (span^(degree i)/(degree i)*rootMass (ν*c) span^(2*rootCount (cs.get i)))≤
    ((cs.length:ℝ)*∑ i : Fin cs.length,
      (MeanRMSTimeFactors.assignmentCoefficient P ell Cs k span fresh A0 i)^2*
        (span^(degree i)/(degree i)*K^(2*rootCount (cs.get i))))*(1+ν)^η
  rw [mul_assoc,Finset.sum_mul]
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  apply Finset.sum_le_sum
  intro i _
  have hh:=mul_le_mul_of_nonneg_left (hpow i)
    (mul_nonneg (sq_nonneg (MeanRMSTimeFactors.assignmentCoefficient P ell Cs k span fresh A0 i))
      (div_nonneg (rpow_nonneg hspan (degree i)) (hd i).le))
  convert! hh using 1 <;> ring

/-- Root-amplitude homogeneity is exact; the frequency-loss constant
at unit amplitude is independent of the actual root function. -/
theorem assignmentFrequencyConstant_amplitude (P : CanonicalCovariance.ProfileParameters) (ell : ℝ) (Cs : ℕ→ℝ)
    (k : ℕ) (ρ span fresh A0 η : ℝ) :
    assignmentFrequencyConstant P ell Cs k ρ span fresh A0 η=
      A0^2*assignmentFrequencyConstant P ell Cs k ρ span fresh 1 η := by
  unfold assignmentFrequencyConstant
  dsimp only
  rw [mul_left_comm (A0^2)]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  unfold MeanRMSTimeFactors.assignmentCoefficient PhysicalAssignmentGapScale.prefactor
  ring
end SHE.PastMeanTimeFactors
