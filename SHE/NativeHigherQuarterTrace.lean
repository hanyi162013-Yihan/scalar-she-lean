module
public import SHE.NativeHigherEnergyFactors
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace SHE.NativeHigherQuarterTrace
open Real

/-- The literal native quarter-row denominator supplies one inverse
newest gap. Only the positive heat age is enlarged to the full width. -/
theorem bound (A Cf ell S N W B age width δ ρ:ℝ)
    (hA:0≤A)(hCf:0≤Cf)(hell:0<ell)(hB:0≤B)
    (hage:0≤age)(haw:age≤width)(hδ:0<δ)(hρ:0≤ρ):
    A*age^ρ*((sqrt (Cf/(ell*(3*δ/4)))*S*(W*N))^2*B)≤
      (A*(4*Cf/(3*ell))*S^2*N^2)*width^ρ*δ⁻¹*W^2*B :=by
  have hden:0<ell*(3*δ/4):=by positivity
  have he:(sqrt (Cf/(ell*(3*δ/4)))*S*(W*N))^2=
      (4*Cf/(3*ell))*S^2*N^2*δ⁻¹*W^2:=by
    rw [mul_pow,mul_pow,Real.sq_sqrt (div_nonneg hCf hden.le),mul_pow]
    field_simp
    <;> ring
  rw [he]
  have hh:=mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hage haw hρ)
    (by positivity : 0≤A*(4*Cf/(3*ell))*S^2*N^2*δ⁻¹*W^2*B)
  convert! hh using 1 <;> ring

end SHE.NativeHigherQuarterTrace
