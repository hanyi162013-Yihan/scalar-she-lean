module
public import SHE.MixedFirstDefectFiniteBandEnergy
public import SHE.DefectGapClockDecay
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace SHE.DefectGapFiniteCoefficient
open Real Filter Topology
open scoped BigOperators

def clock (Λ ρ:ℝ):ℝ:=4+2/ρ+log (2+Λ)
def constant (P:CanonicalCovariance.ProfileParameters)(ell:ℝ)(C:ℕ→ℝ)
    (A η:ℝ)(N:ℕ)(Cs:Fin (N+1)→ℝ):ℝ:=
  ((N+1:ℕ):ℝ)*∑i:Fin (N+1),Cs i^2*
    (A*DefectGapFrequency.constant P ell C (i:ℕ) 1 η*(2:ℝ)^η*((1+(i:ℕ):ℕ):ℝ)^2)^2

theorem constant_nonneg (P:CanonicalCovariance.ProfileParameters)(ell:ℝ)(C:ℕ→ℝ)
    (A η:ℝ)(N:ℕ)(Cs:Fin (N+1)→ℝ):0≤constant P ell C A η N Cs:=by
  apply mul_nonneg (Nat.cast_nonneg _)
  exact Finset.sum_nonneg (fun _ _=>mul_nonneg (sq_nonneg _) (sq_nonneg _))

theorem clock_nonneg {Λ ρ:ℝ}(hΛ:0≤Λ)(hρ:0<ρ):0≤clock Λ ρ:=by
  unfold clock
  have hl:0≤log (2+Λ):=log_nonneg (by linarith)
  positivity

/-- The finite family coefficient has exactly one common logarithmic
clock factor before squaring. All remaining constants are independent
of damping and of the band window/frequency. -/
theorem coefficient_eq (P:CanonicalCovariance.ProfileParameters)(ell:ℝ)(C:ℕ→ℝ)
    (A η Λ ρ:ℝ)(N:ℕ)(Cs:Fin (N+1)→ℝ):
    MixedFirstDefectFiniteBandEnergy.coefficient P ell C A η Λ N ρ Cs=
      constant P ell C A η N Cs*clock Λ ρ^2:=by
  unfold MixedFirstDefectFiniteBandEnergy.coefficient constant
  rw [mul_assoc,Finset.sum_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  unfold DefectGapDyadicCost.coefficient DefectGapBandCost.clock clock
  ring

/-- A genuine high-frequency power beats the complete finite-family
RMS coefficient, for every fixed finite comparison order. -/
theorem rms_tends_zero (P:CanonicalCovariance.ProfileParameters)(ell:ℝ)(C:ℕ→ℝ)
    (A η ρ a:ℝ)(N:ℕ)(Cs:Fin (N+1)→ℝ)(hρ:0<ρ)(ha:0<a):
    Tendsto (fun Λ:ℝ=>sqrt (constant P ell C A η N Cs)*clock Λ ρ*Λ^(-a))
      atTop (𝓝 0):=by
  have hh:=DefectGapClockDecay.tends_zero hρ ha 0
  have he(Λ:ℝ):DefectGapBandCost.clock Λ ρ 0=clock Λ ρ:=by
    unfold DefectGapBandCost.clock clock
    norm_num
  simp_rw [he] at hh
  simpa only [mul_zero,mul_assoc] using hh.const_mul (sqrt (constant P ell C A η N Cs))
end SHE.DefectGapFiniteCoefficient
