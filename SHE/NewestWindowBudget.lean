module
public import SHE.MixedPastNewestFiniteError
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
namespace SHE.NewestWindowBudget
open Set MeasureTheory Real GaussianAssignmentBlocks GaussianFreshAssignments
  PhysicalAssignmentGapScale AllocatedAssignmentKernel CoveredHistoryGeometry PhysicalScoreChain
open scoped BigOperators NNReal

/-- The actual finite newest-error clock budget increases with the
window span: every old block exponent retained in it is nonnegative. -/
theorem current_mono(P:CanonicalCovariance.ProfileParameters){ell:ℝ}(hell:0<ell)
    (C:ℕ→ℝ)(hC:∀j,0≤C j)(n k:ℕ){s t fresh A0:ℝ}(hs:0≤s)(hst:s≤t)
    (hf:0<fresh)(hA:0≤A0)(ν:ℝ):
    PastNewestTimeIntegral.currentConstant P ell C n k s fresh A0 ν≤
      PastNewestTimeIntegral.currentConstant P ell C n k t fresh A0 ν:=by
  let cs:=assignments (m:=k+1) (List.finRange k)
  dsimp only [PastNewestTimeIntegral.currentConstant]
  apply Finset.sum_le_sum
  intro i _hi
  have hd(j:Fin k):0<holderDegree (cs.get i) (List.get_mem cs i) (P.exponent/4) j/2:=
    div_pos (holderDegree_pos_le_one (cs.get i) (List.get_mem cs i)
      (div_pos P.exponent_pos (by norm_num)) (by linarith [P.exponent_le_one]) j).1 (by norm_num)
  have he:0≤(P.exponent/4)*(emptyCount (cs.get i):ℝ):=
    mul_nonneg (div_nonneg P.exponent_pos.le (by norm_num)) (Nat.cast_nonneg _)
  have hpf:0≤prefactor P (cs.get i) A0 n:=prefactor_nonneg P _ hA n
  have hr:=Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hs hst he) hpf)
  have hscore:0≤PhysicalAssignmentGapScale.scorePrefactor ell C k:=
    PhysicalAssignmentGapScale.scorePrefactor_nonneg hell C hC k
  have hmax:0≤(max 1 (ν*sqrt (ProfileVariance.upperConstant*(P.lower/2))))^((k:ℝ)/2):=
    Real.rpow_nonneg (zero_le_one.trans (le_max_left _ _)) _
  have hleft:=mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hr hscore) hmax)
    (div_nonneg (sq_nonneg (((k+1:ℕ):ℝ))) hf.le)
  have hprod:(∏j:Fin k,s^(holderDegree (cs.get i) (List.get_mem cs i) (P.exponent/4) j/2)/
      (holderDegree (cs.get i) (List.get_mem cs i) (P.exponent/4) j/2))≤
    ∏j:Fin k,t^(holderDegree (cs.get i) (List.get_mem cs i) (P.exponent/4) j/2)/
      (holderDegree (cs.get i) (List.get_mem cs i) (P.exponent/4) j/2):=by
    apply Finset.prod_le_prod₀
    · intro j _
      exact div_nonneg (Real.rpow_nonneg hs _) (hd j).le
    · intro j _
      exact div_le_div_of_nonneg_right (Real.rpow_le_rpow hs hst (hd j).le) (hd j).le
  exact mul_le_mul hleft hprod
    (Finset.prod_nonneg (fun j _=>div_nonneg (Real.rpow_nonneg hs _) (hd j).le))
    (mul_nonneg (mul_nonneg (mul_nonneg hscore (sqrt_nonneg _)) hmax)
      (div_nonneg (sq_nonneg _) hf.le))

/-- The same original budget is nonnegative even at the degenerate
initial window, without any stochastic or approximation premise. -/
theorem current_nonneg(P:CanonicalCovariance.ProfileParameters){ell:ℝ}(hell:0<ell)
    (C:ℕ→ℝ)(hC:∀j,0≤C j)(n k:ℕ){s fresh A0:ℝ}(hs:0≤s)
    (hf:0<fresh)(hA:0≤A0)(ν:ℝ):
    0≤PastNewestTimeIntegral.currentConstant P ell C n k s fresh A0 ν:=by
  dsimp only [PastNewestTimeIntegral.currentConstant]
  apply Finset.sum_nonneg
  intro i _
  apply mul_nonneg
  · exact mul_nonneg (mul_nonneg
      (mul_nonneg (PhysicalAssignmentGapScale.scorePrefactor_nonneg hell C hC k) (sqrt_nonneg _))
      (Real.rpow_nonneg (zero_le_one.trans (le_max_left _ _)) _))
      (div_nonneg (sq_nonneg _) hf.le)
  · apply Finset.prod_nonneg
    intro j _
    exact div_nonneg (Real.rpow_nonneg hs _)
      (div_pos (holderDegree_pos_le_one _ (List.get_mem _ _) (div_pos P.exponent_pos (by norm_num))
        (by linarith [P.exponent_le_one]) j).1 (by norm_num)).le

/-- Uniform cap for each actual newest-error squared section, including
the variable initial-window span. The comparison uses only span≤1. -/
theorem section_constant_le_one(P:CanonicalCovariance.ProfileParameters)(κ M:ℝ)
    (v b:ℝ≥0)(hvb:v≤b)(hspan:(b:ℝ)-(v:ℝ)≤1)
    {B Hr A0:ℝ}(hB:0≤B)(hHr:0≤Hr)(hA:0≤A0)(k:ℕ)(B0:ℝ≥0)(ν:ℝ):
    MixedPastNewestCurrentEnergy.constant κ (M:=M) P v b B Hr k B0 A0 ν≤
      MixedPastNewestCurrentEnergy.constant κ (M:=M) P 0 1 B Hr k B0 A0 ν:=by
  have hspan0:0≤(b:ℝ)-(v:ℝ):=sub_nonneg.mpr (by exact_mod_cast hvb)
  have hell:0<ControlledOldIntervals.fraction P*P.lower:=
    mul_pos (ControlledOldIntervals.fraction_pos P) P.lower_pos
  have hcurr0:=current_nonneg P hell (uniformConstant 1) (fresh:=P.exponent/8)
    (fun j=>(uniformConstant_pos 1 j).le) 1 k hspan0
    (div_pos P.exponent_pos (by norm_num)) hA ν
  have hcurr:=current_mono P hell (uniformConstant 1) (fresh:=P.exponent/8)
    (fun j=>(uniformConstant_pos 1 j).le) 1 k hspan0 hspan
    (div_pos P.exponent_pos (by norm_num)) hA ν
  have hh:=mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hcurr0 hcurr 2)
    (mul_nonneg (MixedPastNewestCollision.constant_nonneg κ (M:=M) P hB hHr k B0)
      (sq_nonneg (Fintype.card (OrderedHeatForests.Choices 1 k):ℝ)))
  simpa only [MixedPastNewestCurrentEnergy.constant,NNReal.coe_one,NNReal.coe_zero,sub_zero] using hh

theorem section_constant_nonneg(P:CanonicalCovariance.ProfileParameters)(κ M:ℝ)
    (v b:ℝ≥0){B Hr:ℝ}(hB:0≤B)(hHr:0≤Hr)(k:ℕ)(B0:ℝ≥0)(A0 ν:ℝ):
    0≤MixedPastNewestCurrentEnergy.constant κ (M:=M) P v b B Hr k B0 A0 ν:=
  mul_nonneg
    (mul_nonneg (MixedPastNewestCollision.constant_nonneg κ (M:=M) P hB hHr k B0) (sq_nonneg _))
    (sq_nonneg _)

/-- All finitely many positive ordinary insertion errors have ONE cap
before output time and before the companion smoothing index. -/
theorem finite_constant_le_one(P:CanonicalCovariance.ProfileParameters)(κ M:ℝ)
    (v b:ℝ≥0)(hvb:v≤b)(hspan:(b:ℝ)-(v:ℝ)≤1)
    {B Hr A0:ℝ}(hB:0≤B)(hHr:0≤Hr)(hA:0≤A0)(depth:ℕ)(B0:ℕ→ℝ≥0)(ν:ℝ):
    MixedPastNewestFiniteError.constant P κ M v b B Hr depth B0 A0 ν≤
      MixedPastNewestFiniteError.constant P κ M 0 1 B Hr depth B0 A0 ν:=by
  have hspan0:0≤(b:ℝ)-(v:ℝ):=sub_nonneg.mpr (by exact_mod_cast hvb)
  have hf:0<P.exponent/8:=div_pos P.exponent_pos (by norm_num)
  have hpow:((b:ℝ)-(v:ℝ))^(P.exponent/8)≤1:=Real.rpow_le_one hspan0 hspan hf.le
  have hratio:((b:ℝ)-(v:ℝ))^(P.exponent/8)/(P.exponent/8)≤1/(P.exponent/8):=
    div_le_div_of_nonneg_right hpow hf.le
  have hratio0:0≤((b:ℝ)-(v:ℝ))^(P.exponent/8)/(P.exponent/8):=
    div_nonneg (Real.rpow_nonneg hspan0 _) hf.le
  dsimp only [MixedPastNewestFiniteError.constant]
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg depth)
  apply Finset.sum_le_sum
  intro k _
  have hc:=section_constant_le_one P κ M v b hvb hspan hB hHr hA k (B0 k) ν
  have hh:=mul_le_mul hc (pow_le_pow_left₀ hratio0 hratio 2) (sq_nonneg _)
    (section_constant_nonneg P κ M 0 1 hB hHr k (B0 k) A0 ν)
  simpa only [NNReal.coe_one,NNReal.coe_zero,sub_zero,Real.one_rpow] using hh
end SHE.NewestWindowBudget
