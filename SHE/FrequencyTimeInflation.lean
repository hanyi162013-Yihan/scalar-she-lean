module

public import SHE.PairedBudgetFrequency

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SHE.FrequencyTimeInflation
open Real

def inflate (span ν:ℝ):ℝ:=(1+ν)*span^(-1/4:ℝ)-1

/-- Inflating only an auxiliary jet packet leaves the actual root
function unchanged and permits the native time/frequency estimate. -/
theorem le_inflate {span ν:ℝ} (hs:0<span) (hs1:span≤1) (hν:0≤ν):ν ≤ inflate span ν:=by
  have hp:1≤span^(-1/4:ℝ):=by
    have hh:=rpow_le_rpow_of_nonpos hs hs1 (by norm_num:(-1/4:ℝ)≤0)
    simpa only [one_rpow] using hh
  unfold inflate
  nlinarith

theorem one_add_inflate (span ν:ℝ):1+inflate span ν=(1+ν)*span^(-1/4:ℝ):=by
  unfold inflate
  ring

theorem native_band {span ν:ℝ} (hs:0<span) (hν:0≤ν):
    (1+inflate span ν)^(-4:ℝ)≤span:=by
  rw [one_add_inflate,mul_rpow (by positivity) (rpow_nonneg hs.le _),←rpow_mul hs.le]
  have he:(-1/4:ℝ)*(-4)=1:=by norm_num
  rw [he,rpow_one]
  have hb:(1+ν)^(-4:ℝ)≤1:=by
    have hh:=rpow_le_rpow_of_nonpos (by norm_num:(0:ℝ)<1) (show 1≤1+ν by linarith)
      (by norm_num:(-4:ℝ)≤0)
    simpa only [one_rpow] using hh
  simpa only [one_mul] using mul_le_mul_of_nonneg_right hb hs.le

/-- The cost of the harmless jet inflation is an explicit quarter
power of the local span; every finite-order gain remains visible. -/
theorem weight_identity {span ν:ℝ} (hs:0<span) (hν:0≤ν) (a d:ℝ):
    (1+inflate span ν)^(2*a)*span^d=(1+ν)^(2*a)*span^(d-a/2):=by
  rw [one_add_inflate,mul_rpow (by positivity) (rpow_nonneg hs.le _),←rpow_mul hs.le]
  have he:(-1/4:ℝ)*(2*a)+d=d-a/2:=by ring
  rw [mul_assoc,←rpow_add hs,he]

end SHE.FrequencyTimeInflation
