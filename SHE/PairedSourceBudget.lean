module

public import SHE.PairedSourcePower

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace SHE.PairedSourceBudget
open Real

def coefficient (H β χ ν:ℝ):ℝ:=(ν^χ)^2+(max 1 (H^(χ/β)))^2+(2*H)^(2*χ/β)

theorem coefficient_nonneg {H β χ ν:ℝ} (hH:0≤H):0≤coefficient H β χ ν:=by
  unfold coefficient
  positivity

theorem root_bound {H β χ ν C A E P:ℝ} (hH:0≤H) (hC:0≤C) (hE:0≤E) (hP:0≤P):
    C*((ν^χ)^2*E^χ)*A^2≤C*coefficient H β χ ν*A^2*(E^χ+P^χ):=by
  have he:=rpow_nonneg hE χ
  have hp:=rpow_nonneg hP χ
  have hk:((ν^χ)^2)≤coefficient H β χ ν:=by
    unfold coefficient
    linarith [sq_nonneg (max 1 (H^(χ/β))),rpow_nonneg (by positivity : 0≤2*H) (2*χ/β)]
  have hz:=mul_le_mul_of_nonneg_right hk he
  have hc:=coefficient_nonneg (β:=β) (χ:=χ) (ν:=ν) hH
  have hb:((ν^χ)^2)*E^χ≤coefficient H β χ ν*(E^χ+P^χ):=by
    exact hz.trans (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hp) hc)
  convert! mul_le_mul_of_nonneg_left hb (mul_nonneg hC (sq_nonneg A)) using 1 <;> ring

theorem rough_bound {H β χ ν C A E P:ℝ} (hH:0≤H) (hβ:0<β) (hC:0≤C) (hE:0≤E) (hP:0≤P):
    C*((max 1 (H^(χ/β)))^2*E^χ+((2*H)^2*P^β)^(χ/β))*A^2≤
      C*coefficient H β χ ν*A^2*(E^χ+P^χ):=by
  rw [PairedSourcePower.profile_power hH hP hβ]
  have he:=rpow_nonneg hE χ
  have hp:=rpow_nonneg hP χ
  have h0:0≤(ν^χ)^2:=sq_nonneg _
  have h1:0≤(max 1 (H^(χ/β)))^2:=sq_nonneg _
  have h2:0≤(2*H)^(2*χ/β):=rpow_nonneg (by positivity) _
  have ha:(max 1 (H^(χ/β)))^2≤coefficient H β χ ν:=by unfold coefficient;linarith
  have hb:(2*H)^(2*χ/β)≤coefficient H β χ ν:=by unfold coefficient;linarith
  have hz:=add_le_add (mul_le_mul_of_nonneg_right ha he) (mul_le_mul_of_nonneg_right hb hp)
  convert! mul_le_mul_of_nonneg_left hz (mul_nonneg hC (sq_nonneg A)) using 1 <;> ring

end SHE.PairedSourceBudget
