module

public import SHE.HighFiniteUnweightedRemainder
public import Mathlib.Analysis.SpecificLimits.Normed

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace SHE.DyadicRemainderTail
open Real
open scoped BigOperators

theorem rms_term (J j:ℕ):
    ((2:ℝ)^(J+j))^(-4:ℝ)=((2:ℝ)^J)^(-4:ℝ)*(1/16:ℝ)^j:=by
  rw [pow_add,mul_rpow (by positivity) (by positivity)]
  rw [←rpow_pow_comm (by norm_num:(0:ℝ)≤2) (-4:ℝ) j]
  have he:(2:ℝ)^(-4:ℝ)=1/16:=by norm_num
  rw [he]

/-- Actual R^-8 band energy has R^-4 RMS. Its dyadic RMS tail has
finite constant16/15, uniformly in the finite upper cutoff. -/
theorem hasSum_rms (J:ℕ):
    HasSum (fun j:ℕ=>((2:ℝ)^(J+j))^(-4:ℝ)) ((16/15:ℝ)*((2:ℝ)^J)^(-4:ℝ)):=by
  have hg:=hasSum_geometric_of_abs_lt_one (r:=(1/16:ℝ)) (by norm_num)
  have hh:=hg.mul_left (((2:ℝ)^J)^(-4:ℝ))
  simp_rw [rms_term]
  convert! hh using 1 <;> norm_num <;> ring

theorem tsum_rms (J:ℕ):
    (∑'j:ℕ,((2:ℝ)^(J+j))^(-4:ℝ))=(16/15:ℝ)*((2:ℝ)^J)^(-4:ℝ):=
  (hasSum_rms J).tsum_eq

theorem finite_rms (J L:ℕ):
    (∑j∈Finset.range L,((2:ℝ)^(J+j))^(-4:ℝ))≤(16/15:ℝ)*((2:ℝ)^J)^(-4:ℝ):=by
  rw [←tsum_rms]
  exact (hasSum_rms J).summable.sum_le_tsum (Finset.range L) (fun j _=>rpow_nonneg (by positivity) _)

/-- After the triangle/Minkowski sum is squared, the original R^-8
energy tail is retained, with explicit finite factor256/225. -/
theorem squared_tail (J:ℕ):
    (∑'j:ℕ,((2:ℝ)^(J+j))^(-4:ℝ))^2=(256/225:ℝ)*((2:ℝ)^J)^(-8:ℝ):=by
  rw [tsum_rms,mul_pow]
  have he:((((2:ℝ)^J)^(-4:ℝ))^2)=((2:ℝ)^J)^(-8:ℝ):=by
    rw [←rpow_mul_natCast (show 0≤(2:ℝ)^J by positivity)]
    norm_num
  rw [he]
  norm_num

end SHE.DyadicRemainderTail
