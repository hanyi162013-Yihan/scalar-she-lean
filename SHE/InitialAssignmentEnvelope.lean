module

public import SHE.PairedRMSTimeBudget
public import SHE.PairedPhysicalGapIntegral
public import SHE.AssignedSimplexIntegral

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
noncomputable section
namespace SHE.InitialAssignmentEnvelope
open Set MeasureTheory Real GaussianAssignmentBlocks PhysicalAssignmentGapScale
open scoped BigOperators
open Classical
variable {k:ℕ}

/-- ONE positive old-gap envelope for every output terminal T≤h.
The empty rough ages are enlarged to h, while all old root clips and
all assigned-block minima remain on their original gaps. -/
def kernel (P:CanonicalCovariance.ProfileParameters) (ell:ℝ) (C:ℕ→ℝ)
    (cs:List (Fin k×Fin (k+1))) (h χ A0 ν:ℝ) (i:Fin (k+1)) (d:Fin k→ℝ):ℝ:=
  Fin.cases
    (2*scorePrefactor ell C k*prefactor P cs A0 1*
      h^((P.exponent/4)*(emptyCount cs:ℝ))*
        AllocatedAssignmentKernel.assignedDensity cs (ν*sqrt (ProfileVariance.upperConstant*(P.lower/2)))
          (P.exponent/4) 1 h d)
    (fun j=>scorePrefactor ell C k*PairedPhysicalGapScale.prefactor P cs j χ A0*
      h^(HeterogeneousAssignmentKernel.emptyDegree cs (HeterogeneousAssignmentKernel.pairedDegree P.exponent χ j))*
        HeterogeneousAssignmentKernel.assignedDensity cs (ν*sqrt (ProfileVariance.upperConstant*(P.lower/2)))
          (HeterogeneousAssignmentKernel.pairedDegree P.exponent χ j) 1 h d) i

theorem kernel_measurable (P:CanonicalCovariance.ProfileParameters) (ell:ℝ) (C:ℕ→ℝ)
    (cs:List (Fin k×Fin (k+1))) (h χ A0 ν:ℝ) (i:Fin (k+1)):
    Measurable (kernel P ell C cs h χ A0 ν i):=by
  refine Fin.cases ?_ (fun j=>?_) i
  · exact (AllocatedAssignmentKernel.assignedDensity_measurable cs _ _ _ _).const_mul _
  · exact (HeterogeneousAssignmentKernel.assignedDensity_measurable cs _ _ _ _).const_mul _

theorem kernel_nonneg (P:CanonicalCovariance.ProfileParameters) {ell:ℝ} (hell:0<ell)
    (C:ℕ→ℝ) (hC:∀j,0≤C j) (cs:List (Fin k×Fin (k+1)))
    {h χ A0 ν:ℝ} (hh:0≤h) (hA0:0≤A0) (hν:0≤ν) (i:Fin (k+1)) (d:Fin k→ℝ):
    0≤kernel P ell C cs h χ A0 ν i d:=by
  have hs:=scorePrefactor_nonneg hell C hC k
  have hf:=mul_nonneg hν (sqrt_nonneg (ProfileVariance.upperConstant*(P.lower/2)))
  refine Fin.cases ?_ (fun j=>?_) i
  · exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hs) (prefactor_nonneg P cs hA0 1))
      (rpow_nonneg hh _)) (AllocatedAssignmentKernel.assignedDensity_nonneg cs hf _ _ _ d)
  · exact mul_nonneg (mul_nonneg (mul_nonneg hs (PairedPhysicalGapScale.prefactor_nonneg P cs j χ hA0))
      (rpow_nonneg hh _)) (HeterogeneousAssignmentKernel.assignedDensity_nonneg cs hf _ _ _ d)

/-- The common initial-triangle envelope has EXACTLY the already
proved finite paired time budget, with no new degree or frequency loss. -/
theorem kernel_integral (P:CanonicalCovariance.ProfileParameters) {ell:ℝ} (hell:0<ell)
    (C:ℕ→ℝ) (hC:∀j,0≤C j) (cs:List (Fin k×Fin (k+1)))
    (hc:cs∈assignments (m:=k+1) (List.finRange k))
    {h χ A0 ν:ℝ} (hh:0<h) (hχ:0≤χ) (hχβ:χ<P.exponent) (hA0:0≤A0) (hν:0≤ν)
    (i:Fin (k+1)):
    Integrable (kernel P ell C cs h χ A0 ν i) ∧
      (∫d,kernel P ell C cs h χ A0 ν i d)≤PairedRMSTimeBudget.mass P ell C cs hc h χ A0 ν i:=by
  have hf:=mul_nonneg hν (sqrt_nonneg (ProfileVariance.upperConstant*(P.lower/2)))
  have hs:=scorePrefactor_nonneg hell C hC k
  refine Fin.cases ?_ (fun j=>?_) i
  · have hb:=AllocatedAssignmentKernel.assignedDensity_integral_bound cs hc hf
      (div_pos P.exponent_pos (by norm_num)) (show P.exponent/4≤1 by linarith [P.exponent_le_one])
      zero_lt_one le_rfl hh
    refine ⟨hb.1.const_mul _,?_⟩
    change (∫d,(2*scorePrefactor ell C k*prefactor P cs A0 1*h^((P.exponent/4)*(emptyCount cs:ℝ)))*
      AllocatedAssignmentKernel.assignedDensity cs _ _ _ _ d)≤_
    rw [integral_const_mul]
    have hcoef:0≤2*scorePrefactor ell C k*prefactor P cs A0 1*h^((P.exponent/4)*(emptyCount cs:ℝ)):=
      mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hs) (prefactor_nonneg P cs hA0 1)) (rpow_nonneg hh.le _)
    have he:=mul_le_mul_of_nonneg_left hb.2 hcoef
    apply he.trans_eq
    have hd:(P.exponent/4)*(emptyCount cs:ℝ)+(1+(P.exponent/4)*(AllocatedAssignmentKernel.roughCount cs:ℝ)-1)=
        (k:ℝ)*P.exponent/4:=by
      have hc':(emptyCount cs:ℝ)+(AllocatedAssignmentKernel.roughCount cs:ℝ)=(k:ℝ):=by
        exact_mod_cast PhysicalAssignmentGapScale.empty_rough_count cs
      nlinarith
    simp only [PairedRMSTimeBudget.mass,Fin.cases_zero,div_one]
    calc
      _=(2*scorePrefactor ell C k*prefactor P cs A0 1*
          (((k+1:ℕ):ℝ)^2*AllocatedAssignmentKernel.inverseDegreeProduct cs hc (P.exponent/4)))*
          (h^((P.exponent/4)*(emptyCount cs:ℝ))*h^(1+(P.exponent/4)*(AllocatedAssignmentKernel.roughCount cs:ℝ)-1))*
          rootMass (ν*sqrt (ProfileVariance.upperConstant*(P.lower/2))) h^(AllocatedAssignmentKernel.rootCount cs):=by ring
      _=_:=by rw [←rpow_add hh,hd]
  · have hb:=PairedRemainderTime.paired_density_integral_bound cs hc hf P.exponent_pos P.exponent_le_one hχ hχβ hh j
    refine ⟨?_,?_⟩
    · convert! hb.1.const_mul (scorePrefactor ell C k*PairedPhysicalGapScale.prefactor P cs j χ A0) using 1
      funext d
      dsimp only [kernel,Fin.cases_succ]
      ring
    simp only [kernel,Fin.cases_succ]
    simp_rw [mul_assoc (scorePrefactor ell C k*PairedPhysicalGapScale.prefactor P cs j χ A0)]
    change (∫d,(scorePrefactor ell C k*PairedPhysicalGapScale.prefactor P cs j χ A0)*
      (h^(HeterogeneousAssignmentKernel.emptyDegree cs (HeterogeneousAssignmentKernel.pairedDegree P.exponent χ j))*
        HeterogeneousAssignmentKernel.assignedDensity cs _ _ _ _ d))≤_
    rw [integral_const_mul]
    have he:=mul_le_mul_of_nonneg_left hb.2
      (mul_nonneg hs (PairedPhysicalGapScale.prefactor_nonneg P cs j χ hA0))
    convert! he using 1 <;> simp only [PairedRMSTimeBudget.mass,Fin.cases_succ] <;> ring

end SHE.InitialAssignmentEnvelope
