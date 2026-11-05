module

public import SHE.Parameters
public import SHE.FrequencyTimeInflation

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace SHE.HighFiniteRemainderDegree
open Real

/-- The manuscript's FIXED finite depth makes the actual all-frequency
remainder degree positive with a strict margin. -/
theorem degree_margin {β η:ℝ} (hβ:0<β) (hb:β≤4/25) (hη:0≤η) (hηb:η≤β/4):
    0<(SHE.depth β:ℝ)*β-β/2-η ∧
      -2*β+2*(β/2+η)-(3*β/2)*((SHE.depth β:ℝ)*β-β/2-η)≤-8:=by
  have hp:6≤(SHE.depth β:ℝ)*β^2:=(div_le_iff₀ (sq_pos_of_pos hβ)).mp (SHE.depth_lower β)
  have hN:0≤(SHE.depth β:ℝ):=Nat.cast_nonneg _
  have hb1:β≤1:=by linarith
  have hβ2:β^2≤β:=by nlinarith
  have hηmul:β*η≤β*(β/4):=mul_le_mul_of_nonneg_left hηb hβ.le
  have hpos:0<(SHE.depth β:ℝ)*β-β/2-η:=by
    by_contra hn
    have hx:=mul_nonpos_of_nonneg_of_nonpos hβ.le (le_of_not_gt hn)
    nlinarith
  refine ⟨hpos,?_⟩
  nlinarith

/-- Substituting h=lambda^(-3 beta) into the proved actual
all-frequency word energy retains the explicit finite-depth power. -/
theorem frequency_time_identity {lam β η:ℝ} (hlam:0<lam) :
    lam^(-2*β)*lam^(2*(β/2+η))*(lam^(-3*β))^(((SHE.depth β:ℝ)*β-β/2-η)/2)=
      lam^(-2*β+2*(β/2+η)-(3*β/2)*((SHE.depth β:ℝ)*β-β/2-η)):=by
  rw [←rpow_mul hlam.le,←rpow_add hlam,←rpow_add hlam]
  congr 1
  ring

/-- The actual finite-N remainder frequency/time weight is summable
with room to absorb any sufficiently small logarithmic loss. -/
theorem frequency_decay {lam β η:ℝ} (hlam:1≤lam) (hβ:0<β) (hb:β≤4/25)
    (hη:0≤η) (hηb:η≤β/4):
    lam^(-2*β)*lam^(2*(β/2+η))*(lam^(-3*β))^(((SHE.depth β:ℝ)*β-β/2-η)/2)≤lam^(-8:ℝ):=by
  rw [frequency_time_identity (zero_lt_one.trans_le hlam)]
  exact rpow_le_rpow_of_exponent_le hlam (degree_margin hβ hb hη hηb).2

end SHE.HighFiniteRemainderDegree
