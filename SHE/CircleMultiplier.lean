module

public import SHE.HaarLimit

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace SHE.CircleMultiplier

open MeasureTheory AddCircle CircleHeat FiniteHaar
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩

theorem mulMemLp (c : CircleL2) (U : ℝ)
    (hc : ∀ᵐ y ∂haarAddCircle, ‖c y‖ ≤ U) (v : CircleL2) :
    MemLp (fun y => c y * v y) 2 haarAddCircle := by
  apply (Lp.memLp v).of_le_mul (c := U) ((Lp.aestronglyMeasurable c).mul (Lp.aestronglyMeasurable v))
  filter_upwards [hc] with y hy
  change ‖c y * v y‖ ≤ U * ‖v y‖
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right hy (norm_nonneg _)

def multiply (c : CircleL2) (U : ℝ) (hc : ∀ᵐ y ∂haarAddCircle, ‖c y‖ ≤ U) (v : CircleL2) : CircleL2 :=
  (mulMemLp c U hc v).toLp _

theorem multiply_ae (c : CircleL2) (U : ℝ) (hc : ∀ᵐ y ∂haarAddCircle, ‖c y‖ ≤ U) (v : CircleL2) :
    ⇑(multiply c U hc v) =ᵐ[haarAddCircle] fun y => c y * v y := (mulMemLp c U hc v).coeFn_toLp

def multiplyLinear (c : CircleL2) (U : ℝ) (hc : ∀ᵐ y ∂haarAddCircle, ‖c y‖ ≤ U) : CircleL2 →ₗ[ℂ] CircleL2 where
  toFun := multiply c U hc
  map_add' v w := by
    apply Lp.ext
    filter_upwards [multiply_ae c U hc (v + w), multiply_ae c U hc v, multiply_ae c U hc w,
      Lp.coeFn_add v w, Lp.coeFn_add (multiply c U hc v) (multiply c U hc w)] with y ha hv hw hb hd
    rw [ha, hd]
    simp only [Pi.add_apply, hv, hw, hb, mul_add]
  map_smul' a v := by
    apply Lp.ext
    filter_upwards [multiply_ae c U hc (a • v), multiply_ae c U hc v,
      Lp.coeFn_smul a v, Lp.coeFn_smul a (multiply c U hc v)] with y ha hv hb hd
    simp only [RingHom.id_apply]
    rw [ha, hd]
    simp only [Pi.smul_apply, smul_eq_mul, hv, hb]
    ring

theorem multiply_norm_le (c : CircleL2) (U : ℝ) (hc : ∀ᵐ y ∂haarAddCircle, ‖c y‖ ≤ U) (v : CircleL2) :
    ‖multiply c U hc v‖ ≤ U * ‖v‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [multiply_ae c U hc v, hc] with y hy hb
  rw [hy, norm_mul]
  exact mul_le_mul_of_nonneg_right hb (norm_nonneg _)

/-- Literal pointwise multiplication by a bounded circle `L²` coefficient. -/
def operator (c : CircleL2) (U : ℝ) (hc : ∀ᵐ y ∂haarAddCircle, ‖c y‖ ≤ U) : CircleL2 →L[ℂ] CircleL2 :=
  (multiplyLinear c U hc).mkContinuous U (multiply_norm_le c U hc)

theorem operator_ae (c : CircleL2) (U : ℝ) (hc : ∀ᵐ y ∂haarAddCircle, ‖c y‖ ≤ U) (v : CircleL2) :
    ⇑(operator c U hc v) =ᵐ[haarAddCircle] fun y => c y * v y := multiply_ae c U hc v

theorem elliptic_norm_bound (c : CircleL2) (m U : ℝ) (hm : 0 < m)
    (hcReal : ∀ᵐ y ∂haarAddCircle, (c y).im = 0)
    (hcBound : ∀ᵐ y ∂haarAddCircle, m ≤ (c y).re ∧ (c y).re ≤ U) :
    ∀ᵐ y ∂haarAddCircle, ‖c y‖ ≤ U := by
  filter_upwards [hcReal, hcBound] with y hr hb
  have he : c y = ((c y).re : ℂ) := by apply Complex.ext <;> simp [hr]
  rw [he, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hm.trans_le hb.1).le]
  exact hb.2

theorem inverse_norm_bound (c : CircleL2) (m : ℝ) (hm : 0 < m)
    (hc : ∀ᵐ y ∂haarAddCircle, m ≤ (c y).re) :
    ∀ᵐ y ∂haarAddCircle, ‖(c y)⁻¹‖ ≤ m⁻¹ := by
  filter_upwards [hc] with y hy
  have hn : m ≤ ‖c y‖ := hy.trans (Complex.re_le_norm _)
  rw [norm_inv]
  simpa only [one_div] using one_div_le_one_div_of_le hm hn

theorem inverseMemLp (c : CircleL2) (m : ℝ) (hm : 0 < m)
    (hc : ∀ᵐ y ∂haarAddCircle, m ≤ (c y).re) :
    MemLp (fun y => (c y)⁻¹) 2 haarAddCircle :=
  MemLp.of_bound (Lp.aestronglyMeasurable c).inv₀ (m⁻¹) (inverse_norm_bound c m hm hc)

def inverseCoefficient (c : CircleL2) (m : ℝ) (hm : 0 < m)
    (hc : ∀ᵐ y ∂haarAddCircle, m ≤ (c y).re) : CircleL2 := (inverseMemLp c m hm hc).toLp _

theorem inverseCoefficient_ae (c : CircleL2) (m : ℝ) (hm : 0 < m)
    (hc : ∀ᵐ y ∂haarAddCircle, m ≤ (c y).re) :
    ⇑(inverseCoefficient c m hm hc) =ᵐ[haarAddCircle] fun y => (c y)⁻¹ :=
  (inverseMemLp c m hm hc).coeFn_toLp

theorem inverseCoefficient_bound (c : CircleL2) (m : ℝ) (hm : 0 < m)
    (hc : ∀ᵐ y ∂haarAddCircle, m ≤ (c y).re) :
    ∀ᵐ y ∂haarAddCircle, ‖inverseCoefficient c m hm hc y‖ ≤ m⁻¹ := by
  filter_upwards [inverseCoefficient_ae c m hm hc, inverse_norm_bound c m hm hc] with y hy hb
  simpa only [hy] using hb

def inverseOperator (c : CircleL2) (m : ℝ) (hm : 0 < m)
    (hc : ∀ᵐ y ∂haarAddCircle, m ≤ (c y).re) : CircleL2 →L[ℂ] CircleL2 :=
  operator (inverseCoefficient c m hm hc) (m⁻¹) (inverseCoefficient_bound c m hm hc)

theorem operator_comp_inverse (c : CircleL2) (m U : ℝ) (hm : 0 < m)
    (hcl : ∀ᵐ y ∂haarAddCircle, m ≤ (c y).re)
    (hcu : ∀ᵐ y ∂haarAddCircle, ‖c y‖ ≤ U) :
    (operator c U hcu).comp (inverseOperator c m hm hcl) = ContinuousLinearMap.id ℂ CircleL2 := by
  apply ContinuousLinearMap.ext
  intro v
  apply Lp.ext
  have hi := operator_ae (inverseCoefficient c m hm hcl) _ (inverseCoefficient_bound c m hm hcl) v
  filter_upwards [operator_ae c U hcu (inverseOperator c m hm hcl v), hi,
    inverseCoefficient_ae c m hm hcl, hcl] with y ha hb hc hy
  change operator c U hcu (inverseOperator c m hm hcl v) y = v y
  rw [ha]
  change c y * (operator (inverseCoefficient c m hm hcl) _ _ v y) = _
  rw [hb, hc, ← mul_assoc, mul_inv_cancel₀, one_mul]
  exact Complex.ne_zero_of_re_pos (hm.trans_le hy)

theorem inverse_comp_operator (c : CircleL2) (m U : ℝ) (hm : 0 < m)
    (hcl : ∀ᵐ y ∂haarAddCircle, m ≤ (c y).re)
    (hcu : ∀ᵐ y ∂haarAddCircle, ‖c y‖ ≤ U) :
    (inverseOperator c m hm hcl).comp (operator c U hcu) = ContinuousLinearMap.id ℂ CircleL2 := by
  apply ContinuousLinearMap.ext
  intro v
  apply Lp.ext
  have hi := operator_ae (inverseCoefficient c m hm hcl) _ (inverseCoefficient_bound c m hm hcl)
    (operator c U hcu v)
  filter_upwards [hi, operator_ae c U hcu v, inverseCoefficient_ae c m hm hcl, hcl] with y ha hb hc hy
  change operator (inverseCoefficient c m hm hcl) (m⁻¹) (inverseCoefficient_bound c m hm hcl)
    (operator c U hcu v) y = v y
  rw [ha, hb, hc, ← mul_assoc, inv_mul_cancel₀, one_mul]
  exact Complex.ne_zero_of_re_pos (hm.trans_le hy)

def equivalence (c : CircleL2) (m U : ℝ) (hm : 0 < m)
    (hcl : ∀ᵐ y ∂haarAddCircle, m ≤ (c y).re)
    (hcu : ∀ᵐ y ∂haarAddCircle, ‖c y‖ ≤ U) : CircleL2 ≃L[ℂ] CircleL2 := by
  have hleft (v : CircleL2) : inverseOperator c m hm hcl (operator c U hcu v) = v :=
    congrArg (fun T : CircleL2 →L[ℂ] CircleL2 => T v) (inverse_comp_operator c m U hm hcl hcu)
  have hright (v : CircleL2) : operator c U hcu (inverseOperator c m hm hcl v) = v :=
    congrArg (fun T : CircleL2 →L[ℂ] CircleL2 => T v) (operator_comp_inverse c m U hm hcl hcu)
  exact ContinuousLinearEquiv.ofBijective (operator c U hcu)
    (LinearMap.ker_eq_bot.mpr (Function.LeftInverse.injective hleft))
    (LinearMap.range_eq_top.mpr (Function.RightInverse.surjective hright))

theorem scalar_real_self_inner_im (c z : ℂ) (hc : c.im = 0) : (inner ℂ (c * z) z).im = 0 := by
  rw [RCLike.inner_apply]
  simp only [Complex.mul_im, Complex.mul_re, Complex.conj_re, Complex.conj_im, hc]
  ring

theorem scalar_weighted_pair_square (c : ℂ) (a b : ℝ) :
    (inner ℂ (c * ((a : ℂ) + Complex.I * b)) ((a : ℂ) + Complex.I * b)).re =
      (inner ℂ c (((a ^ 2 + b ^ 2 : ℝ)) : ℂ)).re := by
  rw [RCLike.inner_apply, RCLike.inner_apply]
  simp only [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
    Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
  ring

theorem operator_self_inner_im (c : CircleL2) (U : ℝ)
    (hc : ∀ᵐ y ∂haarAddCircle, ‖c y‖ ≤ U)
    (hcReal : ∀ᵐ y ∂haarAddCircle, (c y).im = 0) (v : CircleL2) :
    (inner ℂ (operator c U hc v) v).im = 0 := by
  have hi := integral_im (L2.integrable_inner (𝕜 := ℂ) (operator c U hc v) v)
  rw [← L2.inner_def] at hi
  change RCLike.im (inner ℂ (operator c U hc v) v) = 0
  rw [← hi]
  apply integral_eq_zero_of_ae
  filter_upwards [operator_ae c U hc v, hcReal] with y hy hr
  rw [hy]
  exact scalar_real_self_inner_im (c y) (v y) hr

theorem operator_complexStep_quadratic (c : CircleL2) (U : ℝ)
    (hc : ∀ᵐ y ∂haarAddCircle, ‖c y‖ ≤ U) (k : ℕ) (a b : Grid k → ℝ) :
    (inner ℂ (operator c U hc (DyadicApproximation.complexGridStep k a b))
      (DyadicApproximation.complexGridStep k a b)).re =
      (inner ℂ c (gridStep k (fun x => (a x) ^ 2 + (b x) ^ 2))).re := by
  let v := DyadicApproximation.complexGridStep k a b
  let z := gridStep k (fun x => (a x) ^ 2 + (b x) ^ 2)
  have hv := L2.integrable_inner (𝕜 := ℂ) (operator c U hc v) v
  have hz := L2.integrable_inner (𝕜 := ℂ) c z
  change RCLike.re (inner ℂ (operator c U hc v) v) = RCLike.re (inner ℂ c z)
  rw [L2.inner_def, L2.inner_def, ← integral_re hv, ← integral_re hz]
  apply integral_congr_ae
  filter_upwards [operator_ae c U hc v,
    Lp.coeFn_add (gridStep k a) (Complex.I • gridStep k b), Lp.coeFn_smul Complex.I (gridStep k b),
    gridStep_ae_cellIndex k a, gridStep_ae_cellIndex k b,
    gridStep_ae_cellIndex k (fun x => (a x) ^ 2 + (b x) ^ 2)] with y hm hadd hmul ha hb hz
  rw [hm]
  dsimp only [v, z, DyadicApproximation.complexGridStep]
  rw [hadd]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hmul ⊢
  rw [hmul, ha, hb, hz]
  exact scalar_weighted_pair_square (c y) _ _

end SHE.CircleMultiplier
