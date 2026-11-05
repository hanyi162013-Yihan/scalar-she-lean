module

public import SHE.HeatL1L2
public import SHE.BoundedHeat

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHE.HeatDominatedOperator
open MeasureTheory AddCircle CircleHeat HeatMarkov
open scoped ENNReal
local instance : Fact (0 < (1:ℝ)) := ⟨zero_lt_one⟩
local instance : Fact ((2:ENNReal) ≠ ⊤) := ⟨by simp⟩

variable {w K : ℝ} (hw : 0 < w) (hK : 0 ≤ K)
variable (A : CircleL2 →L[ℂ] CircleL2)
variable (k : AddCircle (1:ℝ) × AddCircle (1:ℝ) → ℂ) (hk : Measurable k)
variable (hbound : ∀ x y,‖k (x,y)‖ ≤ K*‖kernel w hw (y-x)‖)
variable (hactual : ∀ f : CircleL2,A f =ᵐ[haarAddCircle]
  (fun x => ∫ y : AddCircle (1:ℝ),k (x,y)*f y ∂haarAddCircle))

include hK hk hbound in
theorem product_integrable (f : CircleL2) (x : AddCircle (1:ℝ)) :
    Integrable (fun y : AddCircle (1:ℝ) => k (x,y)*f y) haarAddCircle := by
  have hi : Integrable (fun y : AddCircle (1:ℝ) => ‖kernel w hw (y-x)‖*‖f y‖) haarAddCircle := by
    simpa only [norm_mul] using (BoundedHeat.product_integrable hw f x).norm
  apply (hi.const_mul K).mono'
  · exact (hk.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable.mul (Lp.aestronglyMeasurable f)
  · filter_upwards with y
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_right (hbound x y) (norm_nonneg _)).trans_eq (by ring)

include hK hk hbound hactual in
/-- Literal heat-kernel domination implies pointwise domination by the
actual positive heat evolution of the input's modulus. -/
theorem modulus_domination (f : CircleL2) :
    ∀ᵐ x ∂haarAddCircle,‖A f x‖ ≤ K*‖heat w (CircleModulus.value f) x‖ := by
  filter_upwards [hactual f,CircleModulus.heat_norm_ae hw f] with x hx hm
  rw [hx,hm,← integral_const_mul]
  apply (norm_integral_le_integral_norm _).trans
  have hi : Integrable (fun y : AddCircle (1:ℝ) => ‖kernel w hw (y-x)‖*‖f y‖) haarAddCircle := by
    simpa only [norm_mul] using (BoundedHeat.product_integrable hw f x).norm
  apply integral_mono_ae (product_integrable hw hK k hk hbound f x).norm (hi.const_mul K)
  filter_upwards with y
  rw [norm_mul]
  exact (mul_le_mul_of_nonneg_right (hbound x y) (norm_nonneg _)).trans_eq (by ring)

include hK hk hbound hactual in
theorem norm_le_heat_modulus (f : CircleL2) : ‖A f‖ ≤ K*‖heat w (CircleModulus.value f)‖ := by
  have hi : ‖A f‖ ≤ ‖K • heat w (CircleModulus.value f)‖ := by
    apply Lp.norm_le_norm_of_ae_le
    filter_upwards [modulus_domination hw hK A k hk hbound hactual f,
      Lp.coeFn_smul K (heat w (CircleModulus.value f))] with x hx hs
    rw [hs]
    simpa only [Pi.smul_apply,norm_smul,Real.norm_of_nonneg hK] using hx
  simpa only [norm_smul,Real.norm_of_nonneg hK] using hi

include hK hk hbound hactual in
/-- Actual Schur L² bound for every measurable heat-dominated kernel. -/
theorem norm_sq_le (f : CircleL2) : ‖A f‖^2 ≤ K^2*‖f‖^2 := by
  have hb := (norm_le_heat_modulus hw hK A k hk hbound hactual f).trans
    (mul_le_mul_of_nonneg_left (heat_contraction w (CircleModulus.value f)) hK)
  rw [CircleModulus.norm_eq] at hb
  simpa only [mul_pow] using pow_le_pow_left₀ (norm_nonneg _) hb 2

include hK hk hbound hactual in
theorem normOne_le (f : CircleL2) : normOne (A f) ≤ K*normOne f := by
  have hi (v : CircleL2) : Integrable (v : AddCircle (1:ℝ) → ℂ) haarAddCircle :=
    (Lp.memLp v).integrable (by norm_num : (1:ENNReal) ≤ 2)
  have hb := integral_mono_ae (hi (A f)).norm ((hi (heat w (CircleModulus.value f))).norm.const_mul K)
    (modulus_domination hw hK A k hk hbound hactual f)
  rw [integral_const_mul] at hb
  change normOne (A f) ≤ K*normOne (heat w (CircleModulus.value f)) at hb
  apply hb.trans
  simpa only [CircleModulus.normOne_eq] using mul_le_mul_of_nonneg_left (heat_normOne_le hw (CircleModulus.value f)) hK

include hK hk hbound hactual in
theorem norm_sq_le_normOne (hw1 : w ≤ 1) (f : CircleL2) :
    ‖A f‖^2 ≤ HeatL1L2.constant*K^2*w^(-(1/2:ℝ))*normOne f^2 := by
  have hb := pow_le_pow_left₀ (norm_nonneg _) (norm_le_heat_modulus hw hK A k hk hbound hactual f) 2
  rw [mul_pow] at hb
  have hs := mul_le_mul_of_nonneg_left (HeatL1L2.norm_sq_bound hw hw1 (CircleModulus.value f)) (sq_nonneg K)
  rw [CircleModulus.normOne_eq] at hs
  exact hb.trans (hs.trans_eq (by ring))

end SHE.HeatDominatedOperator
