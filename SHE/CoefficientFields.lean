module

public import SHE.StateSmoothing
public import Mathlib.MeasureTheory.Measure.SeparableMeasure
public import Mathlib.Topology.UniformSpace.UniformApproximation

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace SHE.CoefficientFields
open MeasureTheory AddCircle CircleHeat LowBands StateSmoothing GaussianAudit
open scoped ENNReal NNReal Topology
local instance : Fact (0 < (1:ℝ)) := ⟨zero_lt_one⟩
local instance : Fact ((2:ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩
local instance : MeasurableSpace StateL2 := borel StateL2
local instance : BorelSpace StateL2 := ⟨rfl⟩
local instance : MeasurableSpace CircleL2 := borel CircleL2
local instance : BorelSpace CircleL2 := ⟨rfl⟩

theorem coefficient_memLp (a : ℝ → ℝ) (ha : Measurable a) (M : ℝ)
    (hM : ∀ x, |a x| ≤ M) (U : StateL2) :
    MemLp (fun y => (a (U y):ℂ)) 2 (haarAddCircle (T:=1)) := by
  have hM0 : 0 ≤ M := (abs_nonneg (a 0)).trans (hM 0)
  have hm : AEMeasurable (fun y => (a (U y):ℂ)) (haarAddCircle (T:=1)) :=
    (Complex.measurable_ofReal.comp ha).comp_aemeasurable (Lp.aestronglyMeasurable U).aemeasurable
  apply (memLp_const M).of_le hm.aestronglyMeasurable
  exact ae_of_all _ (fun y => by
    simpa only [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hM0] using hM (U y))

/-- The actual nonlinear coefficient field on an arbitrary real `L²`
state, defined directly from the measurable bounded coefficient. -/
def coefficient (a : ℝ → ℝ) (ha : Measurable a) (M : ℝ)
    (hM : ∀ x, |a x| ≤ M) (U : StateL2) : CircleL2 :=
  (coefficient_memLp a ha M hM U).toLp _

theorem coefficient_ae (a : ℝ → ℝ) (ha : Measurable a) (M : ℝ)
    (hM : ∀ x, |a x| ≤ M) (U : StateL2) :
    coefficient a ha M hM U =ᵐ[haarAddCircle] fun y => (a (U y):ℂ) :=
  (coefficient_memLp a ha M hM U).coeFn_toLp

theorem coefficient_real (a : ℝ → ℝ) (ha : Measurable a) (M : ℝ)
    (hM : ∀ x, |a x| ≤ M) (U : StateL2) :
    ∀ᵐ y ∂haarAddCircle, (coefficient a ha M hM U y).im = 0 := by
  filter_upwards [coefficient_ae a ha M hM U] with y hy
  rw [hy]
  rfl

theorem coefficient_elliptic (a : ℝ → ℝ) (ha : Measurable a) (M : ℝ)
    (hM : ∀ x, |a x| ≤ M) (U : StateL2) (m B : ℝ)
    (hmB : ∀ x, m ≤ a x ∧ a x ≤ B) :
    ∀ᵐ y ∂haarAddCircle, m ≤ (coefficient a ha M hM U y).re ∧
      (coefficient a ha M hM U y).re ≤ B := by
  filter_upwards [coefficient_ae a ha M hM U] with y hy
  rw [hy]
  exact hmB (U y)

/-- A uniform scalar approximation error gives the same actual physical
`L²` approximation error, for every input state. -/
theorem coefficient_uniform_error (a b : ℝ → ℝ) (ha : Measurable a) (hb : Measurable b)
    (A B : ℝ) (hA : ∀ x, |a x| ≤ A) (hB : ∀ x, |b x| ≤ B)
    (U : StateL2) {ε : ℝ} (hε : 0 ≤ ε) (he : ∀ x, |a x-b x| ≤ ε) :
    ‖coefficient a ha A hA U-coefficient b hb B hB U‖ ≤ ε := by
  have hae : ∀ᵐ y ∂haarAddCircle,
      ‖(coefficient a ha A hA U-coefficient b hb B hB U) y‖ ≤ ε := by
    filter_upwards [Lp.coeFn_sub (coefficient a ha A hA U) (coefficient b hb B hB U),
      coefficient_ae a ha A hA U,coefficient_ae b hb B hB U] with y hy hya hyb
    rw [hy]
    change ‖coefficient a ha A hA U y-coefficient b hb B hB U y‖ ≤ ε
    rw [hya,hyb,← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs]
    exact he (U y)
  simpa [measureUnivNNReal] using Lp.norm_le_of_ae_bound hε hae

theorem coefficient_lipschitz_bound (a : ℝ → ℝ) (ha : Measurable a) (M : ℝ)
    (hM : ∀ x, |a x| ≤ M) {L : ℝ≥0}
    (hL : LipschitzWith L (fun x => (a x:ℂ))) (U V : StateL2) :
    ‖coefficient a ha M hM U-coefficient a ha M hM V‖ ≤ (L:ℝ)*‖U-V‖ := by
  have he : coefficient a ha M hM U-coefficient a ha M hM V =
      composeBand (fun x => (a x:ℂ)) hL U-composeBand (fun x => (a x:ℂ)) hL V := by
    apply Lp.ext
    filter_upwards [Lp.coeFn_sub (coefficient a ha M hM U) (coefficient a ha M hM V),
      coefficient_ae a ha M hM U,coefficient_ae a ha M hM V,
      composeBand_difference_ae (fun x => (a x:ℂ)) hL U V] with y hy hu hv hb
    rw [hy]
    change coefficient a ha M hM U y-coefficient a ha M hM V y = _
    rw [hu,hv,hb]
  rw [he]
  exact composeBand_difference_norm (fun x => (a x:ℂ)) hL U V

theorem coefficient_lipschitzWith (a : ℝ → ℝ) (ha : Measurable a) (M : ℝ)
    (hM : ∀ x, |a x| ≤ M) {L : ℝ≥0}
    (hL : LipschitzWith L (fun x => (a x:ℂ))) :
    LipschitzWith L (coefficient a ha M hM) := by
  apply LipschitzWith.of_dist_le_mul
  intro U V
  simpa only [dist_eq_norm] using coefficient_lipschitz_bound a ha M hM hL U V

def dyadicCoefficient (N : ℕ) (a : ℝ → ℝ) (ha : Measurable a) (M : ℝ)
    (hM : ∀ x, |a x| ≤ M) : StateL2 → CircleL2 :=
  coefficient (mollify ((2:ℝ)^N) a) (measurable_mollify (by positivity) a ha hM)
    M (mollify_bounded _ a hM)

theorem dyadicCoefficient_continuous {β H M : ℝ} (hβ : 0 ≤ β) (hH : 0 ≤ H)
    (a : ℝ → ℝ) (ha : Measurable a) (hM : ∀ x, |a x| ≤ M)
    (hholder : ∀ x y, |a x-a y| ≤ H*|x-y|^β) (N : ℕ) :
    Continuous (dyadicCoefficient N a ha M hM) :=
  (coefficient_lipschitzWith _ _ M (mollify_bounded _ a hM)
    (mollify_lipschitzWith (by positivity) hβ hH a ha hM hholder)).continuous

theorem coefficient_mollify_error {β H M : ℝ} (hβ : 0 ≤ β) (hH : 0 ≤ H)
    (a : ℝ → ℝ) (ha : Measurable a) (hM : ∀ x, |a x| ≤ M)
    (hholder : ∀ x y, |a x-a y| ≤ H*|x-y|^β) (N : ℕ) (U : StateL2) :
    ‖coefficient a ha M hM U-dyadicCoefficient N a ha M hM U‖ ≤
      H*gaussianAbsMoment β*((2:ℝ)^N)^(-β) := by
  apply coefficient_uniform_error a (mollify ((2:ℝ)^N) a) ha
    (measurable_mollify (by positivity) a ha hM) M M hM (mollify_bounded _ a hM) U
    (mul_nonneg (mul_nonneg hH (gaussianAbsMoment_nonneg _)) (by positivity))
  intro x
  simpa only [abs_sub_comm] using mollify_error (by positivity) hβ hH a ha hM hholder x

theorem dyadic_error_tendsto {β : ℝ} (hβ : 0 < β) (H : ℝ) :
    Filter.Tendsto (fun N : ℕ => H*gaussianAbsMoment β*((2:ℝ)^N)^(-β))
      Filter.atTop (𝓝 (0:ℝ)) := by
  have hr := StateBands.geometric_ratio hβ
  have hh := tendsto_pow_atTop_nhds_zero_of_lt_one hr.1.le hr.2
  have hm := hh.const_mul (H*gaussianAbsMoment β)
  simpa only [mul_zero,Real.rpow_pow_comm (by norm_num : (0:ℝ) ≤ 2)] using hm

/-- The actual rough coefficient map on `L²` is continuous. The proof
constructs a uniformly convergent sequence of actual Lipschitz smooth
coefficient maps, so no nonlinear composition continuity is assumed. -/
theorem coefficient_continuous {β H M : ℝ} (hβ : 0 < β) (hH : 0 ≤ H)
    (a : ℝ → ℝ) (ha : Measurable a) (hM : ∀ x, |a x| ≤ M)
    (hholder : ∀ x y, |a x-a y| ≤ H*|x-y|^β) :
    Continuous (coefficient a ha M hM) := by
  have hunif : TendstoUniformly (fun N => dyadicCoefficient N a ha M hM)
      (coefficient a ha M hM) Filter.atTop := by
    apply Metric.tendstoUniformly_iff.mpr
    intro ε hε
    have hevent := (dyadic_error_tendsto hβ H).eventually (gt_mem_nhds hε)
    filter_upwards [hevent] with N hN U
    rw [dist_eq_norm]
    exact (coefficient_mollify_error hβ.le hH a ha hM hholder N U).trans_lt hN
  exact hunif.continuous (Filter.Eventually.frequently (Filter.Eventually.of_forall
    (dyadicCoefficient_continuous hβ.le hH a ha hM hholder)))

theorem measurable_coefficient {β H M : ℝ} (hβ : 0 < β) (hH : 0 ≤ H)
    (a : ℝ → ℝ) (ha : Measurable a) (hM : ∀ x, |a x| ≤ M)
    (hholder : ∀ x y, |a x-a y| ≤ H*|x-y|^β) :
    Measurable (coefficient a ha M hM) :=
  (coefficient_continuous hβ hH a ha hM hholder).measurable

/-- Applying the coefficient to a measurable state process is measurable
for any input sigma algebra, including a predictable sigma algebra. -/
theorem measurable_coefficient_process {Ω : Type*} [MeasurableSpace Ω]
    {β H M : ℝ} (hβ : 0 < β) (hH : 0 ≤ H)
    (a : ℝ → ℝ) (ha : Measurable a) (hM : ∀ x, |a x| ≤ M)
    (hholder : ∀ x y, |a x-a y| ≤ H*|x-y|^β)
    (U : Ω → StateL2) (hU : Measurable U) :
    Measurable (fun ω => coefficient a ha M hM (U ω)) :=
  (measurable_coefficient hβ hH a ha hM hholder).comp hU

end SHE.CoefficientFields
