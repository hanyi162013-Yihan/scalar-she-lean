module

public import SHE.RandomProfilePairSource

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace SHE.PairedSourcePower
open Real

/-- The actual Holder profile source retains precisely the true past
second energy to power chi after the correlated Holder step. -/
theorem profile_power {H E β χ:ℝ} (hH:0≤H) (hE:0≤E) (hβ:0<β):
    ((2*H)^2*E^β)^(χ/β)=(2*H)^(2*χ/β)*E^χ:=by
  rw [Real.mul_rpow (sq_nonneg _) (Real.rpow_nonneg hE _),
    ←Real.rpow_natCast_mul (by positivity : 0≤2*H) 2,
    ←Real.rpow_mul hE]
  have hb:β*(χ/β)=χ:=by field_simp [hβ.ne']
  rw [hb]
  congr 1
  ring

end SHE.PairedSourcePower
