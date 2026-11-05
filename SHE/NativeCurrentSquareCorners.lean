module

public import SHE.MeanFreshBudget
public import SHE.AssignedSquareCorners
public import SHE.RootMassFrequency

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
noncomputable section

namespace SHE.NativeCurrentSquareCorners
open Set MeasureTheory Real GaussianAssignmentBlocks AssignmentGapPartition
  AllocatedAssignmentKernel MeanRMSTimeFactors
open scoped BigOperators

/-- A nonempty rough block supplies the exact beta margin. In the
all-root branch the genuine vanishing root mass supplies the margin. -/
theorem assignment_degree_pos {k:ℕ}(cs:List (Fin k×Fin (k+1)))
    (hc:cs∈assignments (m:=k+1) (List.finRange k))(hk:0<k)
    {ρ χ β:ℝ}(hρ:0<ρ)(hχ:χ<1)(hβ:0<β)(hmargin:χ<β+2*ρ):
    0<(ρ-χ/2+β*(roughCount cs:ℝ)/2)+((2*rootCount cs:ℕ):ℝ)/4:=by
  by_cases hr:roughCount cs=0
  · rw [hr,all_root_count cs hc hr]
    have hkp:(1:ℝ)≤k:=by exact_mod_cast hk
    push_cast
    nlinarith
  · have hrough:(1:ℝ)≤roughCount cs:=by exact_mod_cast Nat.pos_of_ne_zero hr
    have hroot:(0:ℝ)≤rootCount cs:=Nat.cast_nonneg _
    push_cast
    nlinarith

/-- The native-current square corner is a genuine integrable function
in all three degree regimes, including chi greater than 2rho. -/
theorem assignment_integrable {k:ℕ}(cs:List (Fin k×Fin (k+1)))
    (hc:cs∈assignments (m:=k+1) (List.finRange k))(hk:0<k)
    {ρ χ β ν T:ℝ}(hρ:0<ρ)(hχ:χ<1)(hβ:0<β)(hmargin:χ<β+2*ρ)
    (hν:0<ν)(hT:0≤T):
    Integrable (fun w=>squareKernel (ρ-χ/2) β ν (rootCount cs) (roughCount cs) w^2)
      (volume.restrict (Ioc 0 T)):=by
  let d:=ρ-χ/2+β*(roughCount cs:ℝ)/2
  have hi:=weighted_root_integrable (ν:=ν) (d:=d) (m:=2*rootCount cs) hν hT
    (assignment_degree_pos cs hc hk hρ hχ hβ hmargin)
  have he: (fun w=>squareKernel (ρ-χ/2) β ν (rootCount cs) (roughCount cs) w^2)=ᵐ[volume.restrict (Ioc 0 T)]
      (fun w=>w^(d-1)*rootMass ν w^(2*rootCount cs)):=by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with w hw
    unfold squareKernel
    rw [mul_pow,←Real.rpow_mul_natCast hw.1.le,←pow_mul,Nat.mul_comm (rootCount cs) 2]
    congr 2
    dsimp only [d]
    ring
  exact ((intervalIntegrable_iff_integrableOn_Ioc_of_le hT).mp hi).congr he.symm

/-- The actual allocated old-time budget remains square integrable
through the full native-current range chi less than beta plus 2rho.
The all-root corner is handled by its genuine root count. -/
theorem budget_memLp (P:CanonicalCovariance.ProfileParameters)(ell:ℝ)(Cs:ℕ→ℝ)
    (k:ℕ)(hk:0<k)(ρ χ T A0 ν:ℝ)(hρ:0<ρ)(hχ:χ<1)
    (hmargin:χ<P.exponent+2*ρ)(hν:0<ν)(hT:0<T):
    MemLp (fun w=>w^(ρ/2)*QuarterRMSTimeFactors.oldTimeBudget P ell Cs k T (T-w)
      ((2-χ)/4) A0 ν) 2 (volume.restrict (Ioc 0 T)):=by
  let cs:=assignments (m:=k+1) (List.finRange k)
  let v:=ν*Real.sqrt (ProfileVariance.upperConstant*(P.lower/2))
  have hv:0<v:=mul_pos hν (Real.sqrt_pos.mpr (mul_pos ProfileVariance.upperConstant_pos (by linarith [P.lower_pos])))
  let f:=fun i:Fin cs.length=>fun w=>assignmentCoefficient P ell Cs k T ((2-χ)/4) A0 i*
    squareKernel (ρ-χ/2) P.exponent v (rootCount (cs.get i)) (roughCount (cs.get i)) w
  have hp(i:Fin cs.length):MemLp (f i) 2 (volume.restrict (Ioc 0 T)):=by
    have hi:=assignment_integrable (cs.get i) (List.get_mem cs i) hk hρ hχ P.exponent_pos hmargin hv hT.le
    have hm:Measurable (squareKernel (ρ-χ/2) P.exponent v (rootCount (cs.get i)) (roughCount (cs.get i))):=
      (real_rpow_measurable _).mul ((rootMass_measurable v).pow_const _)
    exact ((memLp_two_iff_integrable_sq hm.aestronglyMeasurable).mpr hi).const_mul _
  have hs:=memLp_finsetSum Finset.univ (fun i _=>hp i)
  apply hs.ae_eq
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with w hw
  have he:ρ+2*((2-χ)/4)-1=ρ-χ/2:=by ring
  simpa only [f,he] using (budget_sum_identity P ell Cs k ρ T ((2-χ)/4) A0 ν hw.1).symm

end SHE.NativeCurrentSquareCorners
