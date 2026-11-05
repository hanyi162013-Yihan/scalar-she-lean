module

public import SHE.PairedBudgetFactors
public import SHE.PairedCoefficientFrequency

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section
namespace SHE.PairedBudgetFrequency
open Real GaussianAssignmentBlocks
open scoped NNReal BigOperators
variable {k:ℕ}

def entryConstant (P:CanonicalCovariance.ProfileParameters) (κ M ell:ℝ) (C:ℕ→ℝ)
    (B0:ℝ≥0) (cs:List (Fin k×Fin (k+1)))
    (hc:cs∈assignments (m:=k+1) (List.finRange k)) (χ η:ℝ) (order:ℕ) (i:Fin (k+1)):ℝ:=
  sqrt (PairedRMSWeights.coefficient P κ M B0 cs χ 1 order i)*
    |PairedBudgetFactors.coefficient P ell C cs hc χ 1 i| *
    (PastMeanTimeFactors.frequencyRootConstant P k η)^(AllocatedAssignmentKernel.rootCount cs)

theorem entryConstant_nonneg (P:CanonicalCovariance.ProfileParameters) (κ M ell:ℝ) (C:ℕ→ℝ)
    (B0:ℝ≥0) (cs:List (Fin k×Fin (k+1)))
    (hc:cs∈assignments (m:=k+1) (List.finRange k)) (χ η:ℝ) (hη:0<η)
    (order:ℕ) (i:Fin (k+1)):
    0≤entryConstant P κ M ell C B0 cs hc χ η order i:=by
  unfold entryConstant PastMeanTimeFactors.frequencyRootConstant PastMeanTimeFactors.frequencyEpsilon
  positivity

/-- Every original root/rough term retains its OWN time degree and
only the root source costs a chi frequency power. -/
theorem entry_bound (P:CanonicalCovariance.ProfileParameters) {κ M:ℝ}
    (hκ:0≤κ) (hM:0≤M) (ell:ℝ) (C:ℕ→ℝ) (B0:ℝ≥0)
    (cs:List (Fin k×Fin (k+1))) (hc:cs∈assignments (m:=k+1) (List.finRange k))
    {span χ η A0 ν:ℝ} (hspan:0≤span) (hspan1:span≤1) (hχ:0≤χ) (hη:0<η) (hν:0≤ν)
    (order:ℕ) (i:Fin (k+1)):
    sqrt (PairedRMSWeights.coefficient P κ M B0 cs χ ν order i)*
        PairedRMSTimeBudget.mass P ell C cs hc span χ A0 ν i≤
      |A0| *entryConstant P κ M ell C B0 cs hc χ η order i*
        (1+ν)^(Fin.cases χ (fun _=>0) i+η)*span^(PairedBudgetFactors.degree P k χ i):=by
  let a:=|A0| *|PairedBudgetFactors.coefficient P ell C cs hc χ 1 i|
  let s:=span^(PairedBudgetFactors.degree P k χ i)
  let R:=rootMass (ν*sqrt (ProfileVariance.upperConstant*(P.lower/2))) span^(AllocatedAssignmentKernel.rootCount cs)
  let K:=PastMeanTimeFactors.frequencyRootConstant P k η
  let flag : ℝ:=Fin.cases ((1+ν)^χ) (fun _ : Fin k=>1) i
  have ha:0≤a:=mul_nonneg (abs_nonneg _) (abs_nonneg _)
  have hs:0≤s:=rpow_nonneg hspan _
  have hR:0≤R:=pow_nonneg (rootMass_nonneg (mul_nonneg hν (sqrt_nonneg _)) hspan) _
  have hflag:0≤flag:=by
    dsimp only [flag]
    refine Fin.cases ?_ (fun j=>?_) i
    · exact rpow_nonneg (by positivity) _
    · exact zero_le_one
  have hK:0≤K:=by dsimp [K,PastMeanTimeFactors.frequencyRootConstant,PastMeanTimeFactors.frequencyEpsilon];positivity
  have hm:PairedRMSTimeBudget.mass P ell C cs hc span χ A0 ν i≤a*s*R:=by
    rw [PairedBudgetFactors.mass_factorization,PairedBudgetFactors.coefficient_amplitude]
    have hh:A0*PairedBudgetFactors.coefficient P ell C cs hc χ 1 i≤a:=by
      dsimp only [a]
      rw [←abs_mul]
      exact le_abs_self _
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hh hs) hR
  have hcoef:=PairedCoefficientFrequency.coefficient_bound P hκ hM B0 cs hχ hν order i
  have hr:=PairedBudgetFactors.rootPower_frequency_bound P cs hc hspan hspan1 hν hη
  have hf:flag=(1+ν)^((Fin.cases χ (fun _ : Fin k=>(0:ℝ)) i):ℝ):=by
    dsimp only [flag]
    refine Fin.cases ?_ (fun j=>?_) i
    · rfl
    · simp only [Fin.cases_succ,rpow_zero]
  calc
    _≤sqrt (PairedRMSWeights.coefficient P κ M B0 cs χ ν order i)*(a*s*R):=
      mul_le_mul_of_nonneg_left hm (sqrt_nonneg _)
    _≤(sqrt (PairedRMSWeights.coefficient P κ M B0 cs χ 1 order i)*flag)*(a*s*R):=
      mul_le_mul_of_nonneg_right hcoef (mul_nonneg (mul_nonneg ha hs) hR)
    _≤(sqrt (PairedRMSWeights.coefficient P κ M B0 cs χ 1 order i)*flag)*
        (a*s*(K^(AllocatedAssignmentKernel.rootCount cs)*(1+ν)^η)):=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hr (mul_nonneg ha hs))
        (mul_nonneg (sqrt_nonneg _) hflag)
    _=_:=by
      rw [hf,rpow_add (show 0<1+ν by positivity)]
      dsimp only [entryConstant,a,s,K]
      ring

def constant (P:CanonicalCovariance.ProfileParameters) (κ M ell:ℝ) (C:ℕ→ℝ)
    (k:ℕ) (χ η:ℝ) (order:ℕ) (B0:ℝ≥0):ℝ:=
  let cs:=assignments (m:=k+1) (List.finRange k)
  (1/2:ℝ)^k*sqrt ((cs.length*(k+1):ℕ):ℝ)*
    ∑i:Fin cs.length×Fin (k+1),entryConstant P κ M ell C B0 (cs.get i.1) (List.get_mem cs i.1) χ η order i.2

theorem band_degree_bound (P:CanonicalCovariance.ProfileParameters) (k:ℕ)
    {span χ η ν:ℝ} (hspan:0<span) (hχ:0≤χ) (hν:0≤ν)
    (hband:(1+ν)^(-4:ℝ)≤span) (i:Fin (k+1)):
    (1+ν)^(Fin.cases χ (fun _=>0) i+η)*span^(PairedBudgetFactors.degree P k χ i)≤
      (1+ν)^(χ+η)*span^((k:ℝ)*P.exponent/4):=by
  refine Fin.cases (le_refl _) (fun j=>?_) i
  simp only [Fin.cases_succ,zero_add,PairedBudgetFactors.degree]
  have hb:0<1+ν:=by positivity
  have hh:=rpow_le_rpow_of_nonpos (rpow_pos_of_pos hb (-4)) hband (show -χ/4≤0 by linarith)
  rw [←rpow_mul hb.le] at hh
  have he:(-4:ℝ)*(-χ/4)=χ:=by ring
  rw [he] at hh
  have hs:span^((k:ℝ)*P.exponent/4-χ/4)=span^((k:ℝ)*P.exponent/4)*span^(-χ/4):=by
    rw [←rpow_add hspan]
    congr 1
    ring
  rw [hs,rpow_add hb]
  have hm:=mul_le_mul_of_nonneg_left hh
    (mul_nonneg (rpow_nonneg hb.le η) (rpow_nonneg hspan.le ((k:ℝ)*P.exponent/4)))
  convert! hm using 1 <;> ring

/-- At FIXED finite depth the full rough-leaf gain is recovered on
the native frequency/time band, with only chi plus an arbitrary tiny
root-frequency loss. No recursion degree is hidden in the constant. -/
theorem total_band_bound (P:CanonicalCovariance.ProfileParameters) {κ M:ℝ}
    (hκ:0≤κ) (hM:0≤M) (ell:ℝ) (C:ℕ→ℝ) (k:ℕ)
    {span χ η A0 ν:ℝ} (hspan:0<span) (hspan1:span≤1) (hχ:0≤χ) (hη:0<η)
    (hA0:0≤A0) (hν:0≤ν) (hband:(1+ν)^(-4:ℝ)≤span) (order:ℕ) (B0:ℝ≥0):
    PairedRMSTimeBudget.total P κ M ell C k span χ A0 ν order B0≤
      A0*constant P κ M ell C k χ η order B0*(1+ν)^(χ+η)*span^((k:ℝ)*P.exponent/4):=by
  let cs:=assignments (m:=k+1) (List.finRange k)
  have hb(i:Fin cs.length×Fin (k+1)):=entry_bound (A0:=A0) P hκ hM ell C B0
    (cs.get i.1) (List.get_mem cs i.1) hspan.le hspan1 hχ hη hν order i.2
  have hc(i:Fin cs.length×Fin (k+1)):0≤entryConstant P κ M ell C B0
      (cs.get i.1) (List.get_mem cs i.1) χ η order i.2:=
    entryConstant_nonneg P κ M ell C B0 _ _ χ η hη order i.2
  let pref:=(1/2:ℝ)^k*sqrt ((cs.length*(k+1):ℕ):ℝ)
  have hsum:
      (∑i:Fin cs.length×Fin (k+1),
        sqrt (PairedRMSWeights.coefficient P κ M B0 (cs.get i.1) χ ν order i.2)*
          PairedRMSTimeBudget.mass P ell C (cs.get i.1) (List.get_mem cs i.1) span χ A0 ν i.2)≤
      A0*(∑i:Fin cs.length×Fin (k+1),entryConstant P κ M ell C B0
        (cs.get i.1) (List.get_mem cs i.1) χ η order i.2)*
        (1+ν)^(χ+η)*span^((k:ℝ)*P.exponent/4):=by
    rw [Finset.mul_sum,Finset.sum_mul,Finset.sum_mul]
    apply Finset.sum_le_sum
    intro i _
    have he:=band_degree_bound (η:=η) P k hspan hχ hν hband i.2
    have hh:=mul_le_mul_of_nonneg_left he (mul_nonneg hA0 (hc i))
    have hb':=hb i
    rw [abs_of_nonneg hA0] at hb'
    exact hb'.trans (by convert! hh using 1 <;> ring)
  have hh:=mul_le_mul_of_nonneg_left hsum (show 0≤pref by dsimp only [pref];positivity)
  convert! hh using 1 <;>
    dsimp only [PairedRMSTimeBudget.total,constant,pref,cs] <;> ring

end SHE.PairedBudgetFrequency
