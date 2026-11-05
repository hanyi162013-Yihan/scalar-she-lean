module

public import SHE.NativeCurrentBudgetFrequency

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
noncomputable section
namespace SHE.NativeCurrentBudgetFrequency
open Set MeasureTheory Real GaussianAssignmentBlocks AssignmentGapPartition AllocatedAssignmentKernel
  MeanRMSTimeFactors QuarterRMSTimeFactors PhysicalAssignmentGapScale
open scoped BigOperators

/-- Zero output degree is a genuine clipped-root regime. Its exact
fresh-denominator rescaling reduces to the already integrable interior
parameter pair, retaining every original root and rough assignment. -/
theorem zero_majorant (P:CanonicalCovariance.ProfileParameters)(ell:ℝ)(Cs:ℕ→ℝ)
    (k:ℕ)(ν w:ℝ):
    majorant P ell Cs k 0 0 ν w=(3/4:ℝ)*majorant P ell Cs k (1/4:ℝ) (1/2:ℝ) ν w:=by
  have hc(i:Fin (assignments (m:=k+1) (List.finRange k)).length):
      assignmentCoefficient P ell Cs k 1 ((2-(0:ℝ))/4) 1 i=
        (3/4:ℝ)*assignmentCoefficient P ell Cs k 1 ((2-(1/2:ℝ))/4) 1 i:=by
    dsimp only [assignmentCoefficient]
    norm_num
    ring
  unfold majorant
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [hc]
  norm_num only [show (0:ℝ)-0/2=0 by norm_num,show (1/4:ℝ)-(1/2)/2=0 by norm_num,
    abs_mul,abs_of_pos (by norm_num:(0:ℝ)<3/4)]
  ring

/-- The actual bad endpoint kernel has no spurious positive gap degree.
Its true all-root logarithm costs only an arbitrarily small frequency
loss, uniformly before the band and physical window are chosen. -/
theorem zero_majorant_energy (P:CanonicalCovariance.ProfileParameters)(ell:ℝ)(Cs:ℕ→ℝ)
    (k:ℕ)(hk:0<k)(η:ℝ)(hη:0<η):
    ∃C:ℝ,0<C ∧ ∀ν T:ℝ,0<ν→0<T→T≤1→
      Integrable (fun w=>majorant P ell Cs k 0 0 ν w^2) (volume.restrict (Ioc 0 T)) ∧
      (∫w,majorant P ell Cs k 0 0 ν w^2 ∂volume.restrict (Ioc 0 T))≤C*(1+ν)^η:=by
  obtain ⟨C,hC,hb⟩:=majorant_energy P ell Cs k hk (1/4:ℝ) (1/2:ℝ)
    (by norm_num) (by norm_num) (by linarith [P.exponent_pos]) η hη
  refine ⟨C,hC,?_⟩
  intro ν T hν hT hT1
  have hh:=hb ν T hν hT hT1
  have hi:Integrable (fun w=>majorant P ell Cs k 0 0 ν w^2) (volume.restrict (Ioc 0 T)):=by
    simpa only [zero_majorant,mul_pow] using hh.1.const_mul ((3/4:ℝ)^2)
  refine ⟨hi,?_⟩
  simp_rw [zero_majorant,mul_pow,integral_const_mul]
  have hm:0≤∫w,majorant P ell Cs k (1/4:ℝ) (1/2:ℝ) ν w^2 ∂volume.restrict (Ioc 0 T):=
    integral_nonneg (fun _=>sq_nonneg _)
  have he:max 0 (2*(1/2:ℝ)-4*(1/4:ℝ))+η=η:=by norm_num
  rw [he] at hh
  nlinarith [hh.2]

end SHE.NativeCurrentBudgetFrequency
