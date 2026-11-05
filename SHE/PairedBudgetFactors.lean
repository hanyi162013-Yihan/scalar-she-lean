module

public import SHE.PairedBudgetAmplitude
public import SHE.MeanAssignmentFrequency

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
noncomputable section
namespace SHE.PairedBudgetFactors
open Real GaussianAssignmentBlocks PhysicalAssignmentGapScale
open scoped NNReal BigOperators
variable {k:ℕ}

def degree (P:CanonicalCovariance.ProfileParameters) (k:ℕ) (χ:ℝ) (i:Fin (k+1)):ℝ:=
  Fin.cases ((k:ℝ)*P.exponent/4) (fun _=>(k:ℝ)*P.exponent/4-χ/4) i

def coefficient (P:CanonicalCovariance.ProfileParameters) (ell:ℝ) (C:ℕ→ℝ)
    (cs:List (Fin k×Fin (k+1))) (hc:cs∈assignments (m:=k+1) (List.finRange k))
    (χ A0:ℝ) (i:Fin (k+1)):ℝ:=
  Fin.cases
    (2*scorePrefactor ell C k*prefactor P cs A0 1*
      (((k+1:ℕ):ℝ)^2*AllocatedAssignmentKernel.inverseDegreeProduct cs hc (P.exponent/4)))
    (fun j=>scorePrefactor ell C k*PairedPhysicalGapScale.prefactor P cs j χ A0*
      (((k+1:ℕ):ℝ)^2*HeterogeneousAssignmentKernel.inverseDegreeProduct cs hc
        (HeterogeneousAssignmentKernel.pairedDegree P.exponent χ j))) i

theorem mass_factorization (P:CanonicalCovariance.ProfileParameters) (ell:ℝ) (C:ℕ→ℝ)
    (cs:List (Fin k×Fin (k+1))) (hc:cs∈assignments (m:=k+1) (List.finRange k))
    (span χ A0 ν:ℝ) (i:Fin (k+1)):
    PairedRMSTimeBudget.mass P ell C cs hc span χ A0 ν i=
      coefficient P ell C cs hc χ A0 i*span^(degree P k χ i)*
        rootMass (ν*sqrt (ProfileVariance.upperConstant*(P.lower/2))) span^
          (AllocatedAssignmentKernel.rootCount cs):=by
  refine Fin.cases ?_ (fun j=>?_) i <;>
    simp only [PairedRMSTimeBudget.mass,coefficient,degree,Fin.cases_zero,Fin.cases_succ]

theorem coefficient_amplitude (P:CanonicalCovariance.ProfileParameters) (ell:ℝ) (C:ℕ→ℝ)
    (cs:List (Fin k×Fin (k+1))) (hc:cs∈assignments (m:=k+1) (List.finRange k))
    (χ A0:ℝ) (i:Fin (k+1)):
    coefficient P ell C cs hc χ A0 i=A0*coefficient P ell C cs hc χ 1 i:=by
  refine Fin.cases ?_ (fun j=>?_) i <;>
    simp only [coefficient,Fin.cases_zero,Fin.cases_succ,
      PhysicalAssignmentGapScale.prefactor,PairedPhysicalGapScale.prefactor] <;> ring

/-- At fixed finite depth every original root clip has an arbitrarily
small frequency loss, uniformly in the genuine physical span. -/
theorem rootPower_frequency_bound (P:CanonicalCovariance.ProfileParameters)
    (cs:List (Fin k×Fin (k+1))) (hc:cs∈assignments (m:=k+1) (List.finRange k))
    {span ν η:ℝ} (hspan:0≤span) (hspan1:span≤1) (hν:0≤ν) (hη:0<η):
    rootMass (ν*sqrt (ProfileVariance.upperConstant*(P.lower/2))) span^
        (AllocatedAssignmentKernel.rootCount cs)≤
      (PastMeanTimeFactors.frequencyRootConstant P k η)^(AllocatedAssignmentKernel.rootCount cs)*(1+ν)^η:=by
  let ε:=PastMeanTimeFactors.frequencyEpsilon k η
  let K:=PastMeanTimeFactors.frequencyRootConstant P k η
  have hε:0<ε:=by dsimp [ε,PastMeanTimeFactors.frequencyEpsilon];positivity
  have hK:0≤K:=by dsimp [K,PastMeanTimeFactors.frequencyRootConstant];positivity
  have hr:rootMass (ν*sqrt (ProfileVariance.upperConstant*(P.lower/2))) span≤K*(1+ν)^(4*ε):=
    rootMass_scaled_frequency_bound hν (sqrt_nonneg _) hspan hspan1 hε
  have hp:=pow_le_pow_left₀ (rootMass_nonneg (mul_nonneg hν (sqrt_nonneg _)) hspan)
    hr (AllocatedAssignmentKernel.rootCount cs)
  rw [mul_pow,←rpow_mul_natCast (show 0≤1+ν by positivity)] at hp
  have hc':(AllocatedAssignmentKernel.rootCount cs:ℝ)≤((k+1:ℕ):ℝ):=by
    exact_mod_cast (PastMeanTimeFactors.assignment_rootCount_le cs hc).trans (Nat.le_succ k)
  have he:4*ε*(AllocatedAssignmentKernel.rootCount cs:ℝ)≤η:=by
    have hb:=mul_le_mul_of_nonneg_left (show (AllocatedAssignmentKernel.rootCount cs:ℝ)≤2*((k+1:ℕ):ℝ) by linarith)
      (show 0≤4*ε by positivity)
    have hz:4*ε*(2*((k+1:ℕ):ℝ))=η:=by
      dsimp [ε,PastMeanTimeFactors.frequencyEpsilon]
      field_simp
      <;> ring
    exact hb.trans_eq hz
  exact hp.trans (mul_le_mul_of_nonneg_left
    (rpow_le_rpow_of_exponent_le (show 1≤1+ν by linarith) he)
    (pow_nonneg hK _))

end SHE.PairedBudgetFactors
