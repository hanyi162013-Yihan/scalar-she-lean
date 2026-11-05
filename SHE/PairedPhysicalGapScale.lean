module

public import SHE.HeterogeneousAssignmentGain
public import SHE.PhysicalAssignmentGapScale
public import SHE.PairedRoughVaryingMoments

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2100000
noncomputable section
namespace SHE.PairedPhysicalGapScale
open Set MeasureTheory Real GaussianAssignmentBlocks HeterogeneousAssignmentKernel
open scoped BigOperators
open Classical
variable {k:ℕ}

def leafPrefactor (P:CanonicalCovariance.ProfileParameters) (cs:List (Fin k×Fin (k+1)))
    (j0:Fin k) (χ:ℝ) (j:Fin k):ℝ:=
  if j=j0 then if block cs j.succ=[] then P.holder^(1-χ/P.exponent)
    else (2:ℝ)^(block cs j.succ).length*P.holder*
      (ProfileVariance.upperConstant*(P.lower/2))^((P.exponent-χ)/2)
  else PhysicalAssignmentGapScale.leafPrefactor P cs j

def prefactor (P:CanonicalCovariance.ProfileParameters) (cs:List (Fin k×Fin (k+1)))
    (j0:Fin k) (χ A0:ℝ):ℝ:=
  (2:ℝ)^(block cs 0).length*A0*∏j,leafPrefactor P cs j0 χ j

def leafGain (cs:List (Fin k×Fin (k+1))) (a:Fin (k+1)→ℝ) (age d:Fin k→ℝ) (j:Fin k):ℝ:=
  if h:block cs j.succ=[] then (age j)^(a j.succ)
  else (d (MinimumGapChoice.choose d (block cs j.succ) h))^(a j.succ)

def factor (P:CanonicalCovariance.ProfileParameters) (cs:List (Fin k×Fin (k+1)))
    (j0:Fin k) (χ:ℝ) (d age:Fin k→ℝ) (A0 ν:ℝ):ℝ:=
  VectorPhysicalRoot.scale cs 0 (fun _=>0) d A0 ν (P.lower/2) 1*
    ∏j,PairedRoughVaryingMoments.leafScale P cs j0 χ (fun _=>0) d age (fun j=>j)
      (fun j h=>MinimumGapChoice.blockChoice (fun _=>0) d cs j.succ h) j

theorem full_gain_eq (cs:List (Fin k×Fin (k+1))) (ν:ℝ) (a:Fin (k+1)→ℝ) (d age:Fin k→ℝ):
    gain cs ν a d*emptyGain cs a age=
      (∏j:Fin (block cs 0).length,min 1 (ν*(d ((block cs 0).get j))^(1/4:ℝ)))*
        ∏j,leafGain cs a age d j := by
  rw [gain_eq_root_rough]
  unfold emptyGain
  rw [mul_assoc,←Finset.prod_mul_distrib]
  congr 1
  apply Finset.prod_congr rfl
  intro j _
  by_cases hb:block cs j.succ=[] <;>
    simp only [leafGain,hb,dite_true,dite_false,ite_true,ite_false,one_mul,mul_one]

/-- The actual normalized paired rough factor has EXACTLY the
heterogeneous degree (beta-chi)/4, including its EMPTY full-age block. -/
theorem leafScale_eq (P:CanonicalCovariance.ProfileParameters) (cs:List (Fin k×Fin (k+1)))
    (j0:Fin k) (χ:ℝ) (d age:Fin k→ℝ) (hage:∀j,0≤age j) (j:Fin k):
    PairedRoughVaryingMoments.leafScale P cs j0 χ (fun _=>0) d age (fun j=>j)
      (fun j h=>MinimumGapChoice.blockChoice (fun _=>0) d cs j.succ h) j=
      leafPrefactor P cs j0 χ j*leafGain cs (pairedDegree P.exponent χ j0) age d j := by
  by_cases hj:j=j0
  · subst j
    simp only [PairedRoughVaryingMoments.leafScale,ite_true,leafPrefactor,pairedDegree,ite_true]
    by_cases hb:block cs j0.succ=[]
    · simp only [PairedRoughWordMoments.pairScale,hb,dite_true,ite_true,leafGain,pairedDegree,ite_true]
      rw [Real.mul_rpow P.holder_nonneg (Real.rpow_nonneg (hage j0) _),←Real.rpow_mul (hage j0)]
      congr 1
      have he:P.exponent/4*(1-χ/P.exponent)=(P.exponent-χ)/4 := by
        field_simp [P.exponent_pos.ne']
        <;> ring
      rw [he]
    · simp only [PairedRoughWordMoments.pairScale,hb,dite_false,ite_false,leafGain,
        MinimumGapChoice.blockChoice,sub_zero,pairedDegree,ite_true]
  · simp only [PairedRoughVaryingMoments.leafScale,hj,ite_false,leafPrefactor,
      pairedDegree,Fin.succ_inj,hj,ite_false]
    unfold NativeAssignedLeafMoments.leafScale PhysicalAssignmentGapScale.leafPrefactor leafGain
    split_ifs <;> simp only [MinimumGapChoice.blockChoice,sub_zero,pairedDegree,Fin.succ_inj,hj,ite_false]

theorem factor_eq (P:CanonicalCovariance.ProfileParameters) (cs:List (Fin k×Fin (k+1)))
    (j0:Fin k) (χ:ℝ) (d age:Fin k→ℝ) (hage:∀j,0≤age j) (A0 ν:ℝ):
    factor P cs j0 χ d age A0 ν=prefactor P cs j0 χ A0*
      gain cs (ν*sqrt (ProfileVariance.upperConstant*(P.lower/2))) (pairedDegree P.exponent χ j0) d*
      emptyGain cs (pairedDegree P.exponent χ j0) age := by
  unfold factor
  simp_rw [leafScale_eq P cs j0 χ d age hage]
  rw [Finset.prod_mul_distrib]
  have hr:VectorPhysicalRoot.scale cs 0 (fun _=>0) d A0 ν (P.lower/2) 1=
      (2:ℝ)^(block cs 0).length*A0*
        ∏j:Fin (block cs 0).length,min 1 ((ν*sqrt (ProfileVariance.upperConstant*(P.lower/2)))*
          (d ((block cs 0).get j))^(1/4:ℝ)) := by
    simp only [VectorPhysicalRoot.scale,sub_zero,Nat.cast_one,one_pow,mul_one]
  rw [hr]
  calc
    _=prefactor P cs j0 χ A0*
        ((∏j:Fin (block cs 0).length,min 1 ((ν*sqrt (ProfileVariance.upperConstant*(P.lower/2)))*
          (d ((block cs 0).get j))^(1/4:ℝ)))*
          ∏j,leafGain cs (pairedDegree P.exponent χ j0) age d j) := by unfold prefactor;ring
    _=_ := by rw [←full_gain_eq];ring

/-- Original old inverse gaps times the TRUE paired physical scales
equal the same minimum-block kernel used by the proved simplex theorem. -/
theorem inverse_factor_eq (P:CanonicalCovariance.ProfileParameters) (cs:List (Fin k×Fin (k+1)))
    (hc:cs∈assignments (m:=k+1) (List.finRange k)) (j0:Fin k) (χ:ℝ)
    (d age:Fin k→ℝ) (hage:∀j,0≤age j) (A0 ν:ℝ):
    (∏j,(d j)⁻¹)*factor P cs j0 χ d age A0 ν=
      prefactor P cs j0 χ A0*
        weight cs (ν*sqrt (ProfileVariance.upperConstant*(P.lower/2))) (pairedDegree P.exponent χ j0) d*
          emptyGain cs (pairedDegree P.exponent χ j0) age := by
  rw [factor_eq P cs j0 χ d age hage]
  rw [←inverse_mul_gain_eq_weight cs hc]
  ring

end SHE.PairedPhysicalGapScale
