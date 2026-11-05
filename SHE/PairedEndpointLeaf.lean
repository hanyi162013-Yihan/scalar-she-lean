module

public import SHE.PairedRoughBlocks
public import Mathlib.Analysis.MeanInequalitiesPow

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
noncomputable section

namespace SHE.PairedEndpointLeaf
open Real

/-- Pairing keeps the OWN baseline at both endpoints. The pointwise
current source and the endpoint rough cap are separately retained,
before any correlated Hölder estimate is applied. -/
theorem bound (a : ℝ→ℝ) {H β χ : ℝ} (hH : 0≤H) (hβ : 0<β)
    (hχ : 0≤χ) (hχβ : χ≤β)
    (hholder : ∀ z w,|a z-a w|≤H*|z-w|^β)
    (m e noise oldBaseline newBaseline : ℝ) :
    |(a (m+e+noise)-newBaseline)-(a (m+noise)-oldBaseline)|≤
      (H^(χ/β)*|e|^χ+|newBaseline-oldBaseline|^(χ/β))*
        (|a (m+e+noise)-newBaseline|+|a (m+noise)-oldBaseline|)^(1-χ/β) := by
  let C:=H*|e|^β+|newBaseline-oldBaseline|
  let G:=|a (m+e+noise)-newBaseline|+|a (m+noise)-oldBaseline|
  have ht0 : 0≤χ/β:=div_nonneg hχ hβ.le
  have ht1 : χ/β≤1:=(div_le_one hβ).mpr hχβ
  have hC : 0≤C:=add_nonneg (mul_nonneg hH (rpow_nonneg (abs_nonneg _) _)) (abs_nonneg _)
  have hG : 0≤G:=add_nonneg (abs_nonneg _) (abs_nonneg _)
  have hc : |(a (m+e+noise)-newBaseline)-(a (m+noise)-oldBaseline)|≤C:=by
    have hh:=hholder (m+e+noise) (m+noise)
    rw [show m+e+noise-(m+noise)=e by ring] at hh
    have he : (a (m+e+noise)-newBaseline)-(a (m+noise)-oldBaseline)=
        (a (m+e+noise)-a (m+noise))-(newBaseline-oldBaseline):=by ring
    rw [he]
    exact (abs_sub _ _).trans (add_le_add hh le_rfl)
  have hg : |(a (m+e+noise)-newBaseline)-(a (m+noise)-oldBaseline)|≤G:=abs_sub _ _
  have hm:=PairedRoughBlocks.min_rpow_le hC hG ht0 ht1
  simp only [Real.rpow_one] at hm
  have hp : C^(χ/β)≤H^(χ/β)*|e|^χ+|newBaseline-oldBaseline|^(χ/β):=by
    have hh:=Real.rpow_add_le_add_rpow (a:=H*|e|^β)
      (b:=|newBaseline-oldBaseline|) (p:=χ/β)
      (mul_nonneg hH (rpow_nonneg (abs_nonneg e) β))
      (abs_nonneg (newBaseline-oldBaseline)) ht0 ht1
    have he : β*(χ/β)=χ:=by field_simp
    rw [mul_rpow hH (rpow_nonneg (abs_nonneg e) β),←rpow_mul (abs_nonneg e),
      he] at hh
    exact hh
  exact (le_min hc hg).trans (hm.trans (mul_le_mul_of_nonneg_right hp
    (rpow_nonneg hG (1-χ/β))))

end SHE.PairedEndpointLeaf
