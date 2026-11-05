module
public import SHE.GammaDyadicNormEnvelope
@[expose] public section
noncomputable section
set_option autoImplicit false
namespace SHE.GammaFrequencyThreshold
open Real

theorem power {Λ R p:ℝ}(hΛ:0<Λ)(hR:Λ^(1/4:ℝ)≤R)(hp:0≤p):
    R^(-p)≤Λ^(-p/4):=by
  have hh:=Real.rpow_le_rpow_of_nonpos (Real.rpow_pos_of_pos hΛ (1/4:ℝ)) hR (neg_nonpos.mpr hp)
  rw [←Real.rpow_mul hΛ.le] at hh
  simpa only [show (1/4:ℝ)*(-p)=-p/4 by ring] using hh

/-- Replacing the ACTUAL high dyadic cutoff by the damping threshold
preserves all three Gamma rows. No upper-cutoff comparison is needed
for these decreasing-frequency contributions. -/
theorem three_rows {Λ R β q α C K m:ℝ}(hΛ:0<Λ)(hR:Λ^(1/4:ℝ)≤R)
    (hβ:0<β)(hq:0<q)(hC:0≤C)(hK:0≤K)(hm:0≤m):
    C*(StateBands.geometricConstant β*R^(-β)*K+
      StateBands.rootConstant α*m^α+StateBands.geometricConstant q*R^(-q)*m)≤
    C*(StateBands.geometricConstant β*Λ^(-β/4)*K+
      StateBands.rootConstant α*m^α+StateBands.geometricConstant q*Λ^(-q/4)*m):=by
  have hgβ:0≤StateBands.geometricConstant β:=by
    unfold StateBands.geometricConstant
    exact inv_nonneg.mpr (sub_nonneg.mpr (StateBands.geometric_ratio hβ).2.le)
  have hgq:0≤StateBands.geometricConstant q:=by
    unfold StateBands.geometricConstant
    exact inv_nonneg.mpr (sub_nonneg.mpr (StateBands.geometric_ratio hq).2.le)
  apply mul_le_mul_of_nonneg_left _ hC
  have hb:=mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (power hΛ hR hβ.le) hgβ) hK
  have hh:=mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (power hΛ hR hq.le) hgq) hm
  linarith
end SHE.GammaFrequencyThreshold
