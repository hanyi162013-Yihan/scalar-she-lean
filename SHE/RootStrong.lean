module

public import SHE.HaarMeasurable

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section

namespace SHE.CircleMultiplier
open MeasureTheory AddCircle CircleHeat FiniteHaar
local instance rootStrong_multiplierPeriodPos : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩

theorem operator_sub_fixed_norm_le (c d : CircleL2) (U V M : ℝ)
    (hc : ∀ᵐ y ∂haarAddCircle, ‖c y‖ ≤ U) (hd : ∀ᵐ y ∂haarAddCircle, ‖d y‖ ≤ V)
    (v : CircleL2) (hv : ∀ᵐ y ∂haarAddCircle, ‖v y‖ ≤ M) :
    ‖operator c U hc v - operator d V hd v‖ ≤ M * ‖c - d‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [operator_ae c U hc v, operator_ae d V hd v, hv,
    Lp.coeFn_sub (operator c U hc v) (operator d V hd v), Lp.coeFn_sub c d] with y hc hd hv ho hi
  simp only [Pi.sub_apply] at ho hi
  rw [ho, hi, hc, hd, ← sub_mul, norm_mul]
  nlinarith only [mul_le_mul_of_nonneg_left hv (norm_nonneg (c y - d y))]

theorem sqrt_lower_lipschitz {m a b : ℝ} (hm : 0 < m) (ha : m ≤ a) (hb : m ≤ b) :
    |Real.sqrt a - Real.sqrt b| ≤ (Real.sqrt m)⁻¹ * |a - b| := by
  have hs : 0 < Real.sqrt m := Real.sqrt_pos.mpr hm
  have hden : Real.sqrt m ≤ Real.sqrt a + Real.sqrt b :=
    (Real.sqrt_le_sqrt ha).trans (le_add_of_nonneg_right (Real.sqrt_nonneg b))
  have hd : 0 < Real.sqrt a + Real.sqrt b := hs.trans_le hden
  have hprod : (Real.sqrt a - Real.sqrt b) * (Real.sqrt a + Real.sqrt b) = a - b := by
    nlinarith [Real.sq_sqrt (hm.trans_le ha).le, Real.sq_sqrt (hm.trans_le hb).le]
  calc
    _ = |a - b| / (Real.sqrt a + Real.sqrt b) := by
      apply (eq_div_iff hd.ne').mpr
      rw [← hprod, abs_mul, abs_of_pos hd]
    _ ≤ |a - b| / Real.sqrt m := div_le_div_of_nonneg_left (abs_nonneg _) hs hden
    _ = _ := by ring

end SHE.CircleMultiplier

namespace SHE.FiniteHaar
open Finset MeasureTheory AddCircle CircleHeat
open scoped ENNReal NNReal
local instance rootStrong_periodPos : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance rootStrong_exponentFinite : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩
local instance rootStrong_circleSigma : MeasurableSpace CircleL2 := borel CircleL2
local instance rootStrong_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩
local instance rootStrong_inputSigma : MeasurableSpace HaarInput := borel HaarInput
local instance rootStrong_inputBorel : BorelSpace HaarInput := ⟨rfl⟩

def fieldRootCoefficient (m U : ℝ) (f : EllipticField m U) : CircleL2 :=
  CircleMultiplier.rootCoefficient f.1 U (f.2.2.mono (fun _ h => h.2))

def fieldRootEquivalence (m U : ℝ) (hm : 0 < m) (f : EllipticField m U) : CircleL2 ≃L[ℂ] CircleL2 :=
  CircleMultiplier.rootEquivalence f.1 m U hm (f.2.2.mono (fun _ h => h.1)) (f.2.2.mono (fun _ h => h.2))

theorem fieldRootCoefficient_sub_norm_le (m U : ℝ) (hm : 0 < m) (f g : EllipticField m U) :
    ‖fieldRootCoefficient m U f - fieldRootCoefficient m U g‖ ≤ (Real.sqrt m)⁻¹ * ‖f.1 - g.1‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [CircleMultiplier.rootCoefficient_ae f.1 U (f.2.2.mono (fun _ h => h.2)),
    CircleMultiplier.rootCoefficient_ae g.1 U (g.2.2.mono (fun _ h => h.2)), f.2.2, g.2.2,
    Lp.coeFn_sub (fieldRootCoefficient m U f) (fieldRootCoefficient m U g), Lp.coeFn_sub f.1 g.1]
    with y hf hg hb hc ho hi
  simp only [Pi.sub_apply] at ho hi
  change fieldRootCoefficient m U f y = _ at hf
  change fieldRootCoefficient m U g y = _ at hg
  rw [ho, hi, hf, hg, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  exact (CircleMultiplier.sqrt_lower_lipschitz hm hb.1 hc.1).trans
    (mul_le_mul_of_nonneg_left (by simpa only [Complex.sub_re] using Complex.abs_re_le_norm (f.1 y - g.1 y)) (by positivity))

theorem continuous_fieldRootCoefficient (m U : ℝ) (hm : 0 < m) :
    Continuous (fieldRootCoefficient m U) := by
  let K : ℝ≥0 := ⟨(Real.sqrt m)⁻¹, by positivity⟩
  apply LipschitzWith.continuous (K := K)
  apply LipschitzWith.of_dist_le_mul
  intro f g
  rw [dist_eq_norm]
  dsimp only [K]
  rw [Subtype.dist_eq, dist_eq_norm]
  exact fieldRootCoefficient_sub_norm_le m U hm f g

theorem fieldRoot_action_bound (m U : ℝ) (hm : 0 < m) (f : EllipticField m U) (v : CircleL2) :
    ‖fieldRootEquivalence m U hm f v‖ ≤ Real.sqrt U * ‖v‖ :=
  CircleMultiplier.multiply_norm_le _ _ (CircleMultiplier.rootCoefficient_norm_bound f.1 U
    (f.2.2.mono (fun _ h => h.2))) v

theorem continuous_fieldRoot_bounded_action (m U : ℝ) (hm : 0 < m) (v : CircleL2)
    (M : ℝ) (hM : 0 ≤ M) (hv : ∀ᵐ y ∂haarAddCircle, ‖v y‖ ≤ M) :
    Continuous (fun f : EllipticField m U => fieldRootEquivalence m U hm f v) := by
  let K : ℝ≥0 := ⟨M * (Real.sqrt m)⁻¹, by positivity⟩
  apply LipschitzWith.continuous (K := K)
  apply LipschitzWith.of_dist_le_mul
  intro f g
  rw [dist_eq_norm]
  have hb := CircleMultiplier.operator_sub_fixed_norm_le (fieldRootCoefficient m U f) (fieldRootCoefficient m U g)
    (Real.sqrt U) (Real.sqrt U) M
    (CircleMultiplier.rootCoefficient_norm_bound f.1 U (f.2.2.mono (fun _ h => h.2)))
    (CircleMultiplier.rootCoefficient_norm_bound g.1 U (g.2.2.mono (fun _ h => h.2))) v hv
  calc
    _ ≤ M * ‖fieldRootCoefficient m U f - fieldRootCoefficient m U g‖ := hb
    _ ≤ M * ((Real.sqrt m)⁻¹ * ‖f.1 - g.1‖) :=
      mul_le_mul_of_nonneg_left (fieldRootCoefficient_sub_norm_le m U hm f g) hM
    _ = _ := by
      dsimp only [K]
      rw [Subtype.dist_eq, dist_eq_norm]
      change M * ((Real.sqrt m)⁻¹ * ‖f.1 - g.1‖) = (M * (Real.sqrt m)⁻¹) * ‖f.1 - g.1‖
      ring

theorem gridStep_norm_bound (n : ℕ) (a : Grid n → ℝ) :
    ∀ᵐ y ∂haarAddCircle, ‖gridStep n a y‖ ≤ ‖a‖ := by
  filter_upwards [gridStep_ae_cellIndex n a] with y hy
  rw [hy, Complex.norm_real]
  exact norm_le_pi_norm a _

theorem complexGridStep_norm_bound (n : ℕ) (a b : Grid n → ℝ) :
    ∀ᵐ y ∂haarAddCircle, ‖DyadicApproximation.complexGridStep n a b y‖ ≤ ‖a‖ + ‖b‖ := by
  filter_upwards [gridStep_norm_bound n a, gridStep_norm_bound n b,
    Lp.coeFn_add (gridStep n a) (Complex.I • gridStep n b), Lp.coeFn_smul Complex.I (gridStep n b)] with y ha hb hc hd
  change ‖(gridStep n a + Complex.I • gridStep n b) y‖ ≤ _
  rw [hc]
  change ‖gridStep n a y + (Complex.I • gridStep n b) y‖ ≤ _
  rw [hd]
  calc
    _ ≤ ‖gridStep n a y‖ + ‖(Complex.I • (gridStep n b : AddCircle (1 : ℝ) → ℂ)) y‖ := norm_add_le _ _
    _ ≤ _ := by
      change ‖gridStep n a y‖ + ‖Complex.I * gridStep n b y‖ ≤ _
      rw [norm_mul, Complex.norm_I, one_mul]
      exact add_le_add ha hb

theorem continuous_fieldRoot_action (m U : ℝ) (hm : 0 < m) (v : CircleL2) :
    Continuous (fun f : EllipticField m U => fieldRootEquivalence m U hm f v) := by
  apply StrongOperator.continuous_action_of_approximation
    (fun f : EllipticField m U => (fieldRootEquivalence m U hm f).toContinuousLinearMap)
    (Real.sqrt U) (Real.sqrt_nonneg U) (fieldRoot_action_bound m U hm) v
    (fun N => DyadicApproximation.complexAverage N v) (DyadicApproximation.complexAverage_tendsto v)
  intro N
  apply continuous_fieldRoot_bounded_action m U hm _
    (‖localAverage N (DyadicApproximation.realEmbed (DyadicApproximation.realPart v))‖ +
      ‖localAverage N (DyadicApproximation.realEmbed (DyadicApproximation.imagPart v))‖) (by positivity)
  exact complexGridStep_norm_bound N _ _

theorem continuous_fieldRoot_joint (m U : ℝ) (hm : 0 < m) :
    Continuous (fun p : EllipticField m U × CircleL2 => fieldRootEquivalence m U hm p.1 p.2) :=
  StrongOperator.continuous_joint_action
    (fun f : EllipticField m U => (fieldRootEquivalence m U hm f).toContinuousLinearMap)
    (Real.sqrt U) (Real.sqrt_nonneg U) (fieldRoot_action_bound m U hm) (continuous_fieldRoot_action m U hm)

def fieldInnovation (m U : ℝ) (hm : 0 < m) (f : EllipticField m U) : CircleL2 ≃ₗᵢ[ℂ] HaarInput :=
  innovationRotation f.1 m U hm f.2.1 f.2.2

theorem continuous_fieldInnovation_joint (m U : ℝ) (hm : 0 < m) :
    Continuous (fun p : EllipticField m U × CircleL2 => fieldInnovation m U hm p.1 p.2) := by
  exact (continuous_fieldInverse_joint m U hm).comp
    (continuous_fst.prodMk (continuous_fieldRoot_joint m U hm))

theorem measurable_fieldInnovation_joint (m U : ℝ) (hm : 0 < m) :
    Measurable (fun p : EllipticField m U × CircleL2 => fieldInnovation m U hm p.1 p.2) :=
  (continuous_fieldInnovation_joint m U hm).measurable

theorem measurable_fieldInnovation_process {X : Type*} [MeasurableSpace X]
    (m U : ℝ) (hm : 0 < m) (f : X → EllipticField m U) (hf : Measurable f)
    (v : X → CircleL2) (hv : Measurable v) :
    Measurable (fun p => fieldInnovation m U hm (f p) (v p)) := by
  let g : X → EllipticField m U × CircleL2 := fun p => (f p, v p)
  have hg : Measurable g := hf.prodMk hv
  change Measurable ((fun p : EllipticField m U × CircleL2 => fieldInnovation m U hm p.1 p.2) ∘ g)
  exact (measurable_fieldInnovation_joint m U hm).comp hg

end SHE.FiniteHaar
