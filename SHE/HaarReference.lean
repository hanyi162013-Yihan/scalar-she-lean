module

public import SHE.CanonicalProfileL2
public import SHE.HaarL2Heat
public import SHE.HaarOperator
public import SHE.CircleNormalization

@[expose] public section
set_option autoImplicit false

/-! Literal common-Haar reference rows for the canonical physical profiles.
The unit/2π heat-time conversion is retained explicitly. -/
noncomputable section
namespace SHE.HaarReference
open Set MeasureTheory AddCircle StoppedFourier ProfileL2 GaussianProfile ProfileStability CanonicalProfileL2

local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
local instance : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by simp⟩
local instance : MeasurableSpace CircleL2 := borel CircleL2
local instance : BorelSpace CircleL2 := ⟨rfl⟩
local instance : MeasurableSpace CircleHeat.CircleL2 := borel CircleHeat.CircleL2
local instance : BorelSpace CircleHeat.CircleL2 := ⟨rfl⟩

def heatScale : ℝ := (2 * Real.pi) ^ 2

theorem heatScale_pos : 0 < heatScale := by unfold heatScale; positivity

theorem heatScale_one_le : 1 ≤ heatScale := by
  unfold heatScale
  nlinarith [Real.two_le_pi]

def nativeColumn (f g : CircleL2) (t : ℝ) (q : FiniteHaar.HaarNode) : CircleL2 :=
  CircleNormalization.push (CircleHeat.heat (t / heatScale)
    (FiniteHaar.globalSignedColumn q (CircleNormalization.push.symm f) (CircleNormalization.push.symm g)))

def nativeEnergy (f g : CircleL2) (t : ℝ) : ℝ :=
  ∑' q : FiniteHaar.HaarNode, ‖nativeColumn f g t q‖ ^ 2

theorem nativeEnergy_eq (f g : CircleL2) (t : ℝ) :
    nativeEnergy f g t = FiniteHaar.globalSignedHeatEnergy
      (CircleNormalization.push.symm f) (CircleNormalization.push.symm g) (t / heatScale) := by
  unfold nativeEnergy FiniteHaar.globalSignedHeatEnergy nativeColumn
  simp only [LinearIsometryEquiv.norm_map]

theorem nativeEnergy_nonneg (f g : CircleL2) (t : ℝ) : 0 ≤ nativeEnergy f g t :=
  tsum_nonneg (fun _ => sq_nonneg _)

/-- Each actual native row is the native heat semigroup applied to the
same signed Haar column; the heat-time normalization is exact. -/
theorem nativeColumn_heat (f g : CircleL2) {t : ℝ} (ht : 0 ≤ t) (q : FiniteHaar.HaarNode) :
    nativeColumn f g t q = circleHeatOperator t ht
      (CircleNormalization.push (FiniteHaar.globalSignedColumn q
        (CircleNormalization.push.symm f) (CircleNormalization.push.symm g))) := by
  have he := CircleNormalization.push_heat (t / heatScale) (div_nonneg ht heatScale_pos.le)
    (FiniteHaar.globalSignedColumn q (CircleNormalization.push.symm f) (CircleNormalization.push.symm g))
  have ht' : (2 * Real.pi) ^ 2 * (t / heatScale) = t := by
    change heatScale * (t / heatScale) = t
    field_simp [heatScale_pos.ne']
  simpa only [nativeColumn, ht'] using he

/-- Identification with the literal common-Haar factor on every genuine
noise basis vector. This is not a pointwise square-root coupling. -/
theorem nativeColumn_factor_basis (f g : CircleHeat.CircleL2) (ell M : ℝ) (hell : 0 < ell)
    (hfr : ∀ᵐ x ∂haarAddCircle (T := 1), (f x).im = 0)
    (hgr : ∀ᵐ x ∂haarAddCircle (T := 1), (g x).im = 0)
    (hfb : ∀ᵐ x ∂haarAddCircle (T := 1), ell ≤ (f x).re ∧ (f x).re ≤ M)
    (hgb : ∀ᵐ x ∂haarAddCircle (T := 1), ell ≤ (g x).re ∧ (g x).re ≤ M)
    (t : ℝ) (q : FiniteHaar.HaarNode) :
    CircleNormalization.push (CircleHeat.heat (t / heatScale)
      ((FiniteHaar.factor f ell M hell hfr hfb - FiniteHaar.factor g ell M hell hgr hgb)
        (lp.single 2 q 1))) = nativeColumn (CircleNormalization.push f) (CircleNormalization.push g) t q := by
  simp only [sub_apply, FiniteHaar.factor_single, nativeColumn,
    LinearIsometryEquiv.symm_apply_apply, FiniteHaar.globalSignedColumn]

theorem nativeColumn_measurable (q : FiniteHaar.HaarNode) :
    Measurable (fun p : ℝ × (CircleL2 × CircleL2) => nativeColumn p.2.1 p.2.2 p.1 q) := by
  have hmap := ((measurable_fst : Measurable (fun p : ℝ × (CircleL2 × CircleL2) => p.1)).div_const heatScale).prodMk
      (((CircleNormalization.push.symm.continuous.measurable).comp measurable_snd.fst).prodMk
        ((CircleNormalization.push.symm.continuous.measurable).comp measurable_snd.snd))
  have hm := CircleNormalization.push.continuous.measurable.comp
    ((FiniteHaar.measurable_globalSignedHeatAction q).comp hmap)
  exact hm

theorem nativeEnergy_measurable :
    Measurable (fun p : ℝ × (CircleL2 × CircleL2) => nativeEnergy p.2.1 p.2.2 p.1) :=
  Measurable.tsum (fun q => (nativeColumn_measurable q).norm.pow_const (2 : ℕ))

def rowConstant (ell M : ℝ) : ℝ := FiniteHaar.signedL2HeatConstant ell M * heatScale ^ (1 / 2 : ℝ)

theorem rowConstant_nonneg {ell M : ℝ} (hM : 0 ≤ M) : 0 ≤ rowConstant ell M := by
  unfold rowConstant FiniteHaar.signedL2HeatConstant
  exact mul_nonneg (mul_nonneg (div_nonneg hM (sq_nonneg _)) (sq_nonneg _))
    (Real.rpow_nonneg heatScale_pos.le _)

theorem nativeEnergy_bound (f g : CircleL2) {ell M t : ℝ}
    (hell : 0 < ell) (_hM : 0 ≤ M) (ht : 0 < t) (ht1 : t ≤ 1)
    (hfr : ∀ᵐ x ∂haarAddCircle, (f x).im = 0)
    (hgr : ∀ᵐ x ∂haarAddCircle, (g x).im = 0)
    (hfb : ∀ᵐ x ∂haarAddCircle, ell ≤ (f x).re ∧ (f x).re ≤ M)
    (hgb : ∀ᵐ x ∂haarAddCircle, ell ≤ (g x).re ∧ (g x).re ≤ M) :
    nativeEnergy f g t ≤ rowConstant ell M * t ^ (-(1 / 2 : ℝ)) * ‖f - g‖ ^ 2 := by
  have hfreal := CircleNormalization.push_symm_ae_property f (fun z => z.im = 0) hfr
  have hgreal := CircleNormalization.push_symm_ae_property g (fun z => z.im = 0) hgr
  have hfbound := CircleNormalization.push_symm_ae_property f (fun z => ell ≤ z.re ∧ z.re ≤ M) hfb
  have hgbound := CircleNormalization.push_symm_ae_property g (fun z => ell ≤ z.re ∧ z.re ≤ M) hgb
  have he := (FiniteHaar.global_signed_heat_L2 (div_pos ht heatScale_pos)
    ((div_le_one₀ heatScale_pos).mpr (ht1.trans heatScale_one_le)) _ _ ell M hell
      hfreal hgreal hfbound hgbound).2
  have hnorm : ‖CircleNormalization.push.symm f - CircleNormalization.push.symm g‖ = ‖f - g‖ := by
    rw [← map_sub, LinearIsometryEquiv.norm_map]
  have hp : (t / heatScale) ^ (-(1 / 2 : ℝ)) = heatScale ^ (1 / 2 : ℝ) * t ^ (-(1 / 2 : ℝ)) := by
    rw [Real.div_rpow ht.le heatScale_pos.le, div_eq_mul_inv, ← Real.rpow_neg heatScale_pos.le]
    ring_nf
  change FiniteHaar.globalSignedHeatEnergy _ _ _ ≤ _ at he
  rw [hnorm, hp] at he
  rw [nativeEnergy_eq]
  convert he using 1
  unfold rowConstant
  ring

theorem nativeColumns_summable (f g : CircleL2) {ell M t : ℝ}
    (hell : 0 < ell) (ht : 0 < t) (ht1 : t ≤ 1)
    (hfr : ∀ᵐ x ∂haarAddCircle, (f x).im = 0)
    (hgr : ∀ᵐ x ∂haarAddCircle, (g x).im = 0)
    (hfb : ∀ᵐ x ∂haarAddCircle, ell ≤ (f x).re ∧ (f x).re ≤ M)
    (hgb : ∀ᵐ x ∂haarAddCircle, ell ≤ (g x).re ∧ (g x).re ≤ M) :
    Summable (fun q => ‖nativeColumn f g t q‖ ^ 2) := by
  have hfreal := CircleNormalization.push_symm_ae_property f (fun z => z.im = 0) hfr
  have hgreal := CircleNormalization.push_symm_ae_property g (fun z => z.im = 0) hgr
  have hfbound := CircleNormalization.push_symm_ae_property f (fun z => ell ≤ z.re ∧ z.re ≤ M) hfb
  have hgbound := CircleNormalization.push_symm_ae_property g (fun z => ell ≤ z.re ∧ z.re ≤ M) hgb
  have he := (FiniteHaar.global_signed_heat_L2 (div_pos ht heatScale_pos)
    ((div_le_one₀ heatScale_pos).mpr (ht1.trans heatScale_one_le)) _ _ ell M hell
      hfreal hgreal hfbound hgbound).1
  simpa only [nativeColumn, LinearIsometryEquiv.norm_map] using he

/-- The actual common-Haar row is time integrable, with the exact profile
power gain; the countable noise sum is retained in the definition. -/
theorem nativeEnergy_time_bound {f g : ℝ → CircleL2} {ell M β h P D : ℝ}
    (hf : Measurable f) (hg : Measurable g) (hell : 0 < ell) (hM : 0 ≤ M)
    (hfr : ∀ s, ∀ᵐ x ∂haarAddCircle, (f s x).im = 0)
    (hgr : ∀ s, ∀ᵐ x ∂haarAddCircle, (g s x).im = 0)
    (hfb : ∀ s, ∀ᵐ x ∂haarAddCircle, ell ≤ (f s x).re ∧ (f s x).re ≤ M)
    (hgb : ∀ s, ∀ᵐ x ∂haarAddCircle, ell ≤ (g s x).re ∧ (g s x).re ≤ M)
    (hβ : -1 < β) (hh : 0 < h) (hh1 : h ≤ 1) (hP : 0 ≤ P) (hD : 0 ≤ D)
    (hprofile : ∀ s ∈ Ioo 0 h, ‖f s - g s‖ ≤ P * D * s ^ ((β - 1) / 4)) :
    IntervalIntegrable (fun s => nativeEnergy (f s) (g s) (h - s)) volume 0 h ∧
      (∫ s in (0 : ℝ)..h, nativeEnergy (f s) (g s) (h - s)) ≤
        rowConstant ell M * P ^ 2 * ProfileVolterra.powerConstant ((β - 1) / 2) *
          h ^ (β / 2) * D ^ 2 := by
  have hconv := ProfileVolterra.squared_profile_convolution_bound hβ hh hP hD
    (hf.sub hg).norm (fun _ _ => norm_nonneg _) hprofile
  have hm := nativeEnergy_measurable.comp (((measurable_const (a := h)).sub measurable_id).prodMk (hf.prodMk hg))
  have hrow (s : ℝ) (hs : s ∈ Ioo 0 h) :
      nativeEnergy (f s) (g s) (h - s) ≤ rowConstant ell M *
        ((h - s) ^ (-(1 / 2 : ℝ)) * ‖f s - g s‖ ^ 2) := by
    simpa only [mul_assoc] using nativeEnergy_bound (f s) (g s) hell hM
      (sub_pos.mpr hs.2) (by linarith [hs.1]) (hfr s) (hgr s) (hfb s) (hgb s)
  have hi : IntervalIntegrable (fun s => nativeEnergy (f s) (g s) (h - s)) volume 0 h := by
    apply (hconv.1.const_mul (rowConstant ell M)).mono_fun'
    · exact hm.aestronglyMeasurable
    · rw [uIoc_of_le hh.le]
      filter_upwards [ae_restrict_mem measurableSet_Ioc,
        ae_restrict_of_ae (volume.ae_ne h)] with s hs hsh
      rw [Real.norm_eq_abs, abs_of_nonneg (nativeEnergy_nonneg _ _ _)]
      exact hrow s ⟨hs.1, lt_of_le_of_ne hs.2 hsh⟩
  refine ⟨hi, ?_⟩
  calc
    _ ≤ ∫ s in (0 : ℝ)..h, rowConstant ell M * ((h - s) ^ (-(1 / 2 : ℝ)) * ‖f s - g s‖ ^ 2) :=
      intervalIntegral.integral_mono_on_of_le_Ioo hh.le hi
        (hconv.1.const_mul (rowConstant ell M)) hrow
    _ = rowConstant ell M * (∫ s in (0 : ℝ)..h, (h - s) ^ (-(1 / 2 : ℝ)) * ‖f s - g s‖ ^ 2) :=
      intervalIntegral.integral_const_mul _ _
    _ ≤ rowConstant ell M * (P ^ 2 * D ^ 2 * ProfileVolterra.powerConstant ((β - 1) / 2) * h ^ (β / 2)) :=
      mul_le_mul_of_nonneg_left hconv.2 (rowConstant_nonneg hM)
    _ = _ := by ring

def profileRow (a : ℝ → ℝ) (ell h : ℝ) (u v : CircleL2) (r s : ℝ) : ℝ :=
  nativeEnergy (l2Profile a ell h (u, s)) (l2Profile a ell h (v, s)) (r - s)

def referenceConstant (ell M H β : ℝ) : ℝ :=
  4 * rowConstant ell M * meanConstant ell H β ^ 2 * ProfileVolterra.powerConstant ((β - 1) / 2)

theorem referenceConstant_nonneg {ell M H β : ℝ} (hM : 0 ≤ M) (hβ : -1 < β) :
    0 ≤ referenceConstant ell M H β :=
  mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (rowConstant_nonneg hM)) (sq_nonneg _))
    (ProfileVolterra.powerConstant_pos (by linarith)).le

/-- Literal same-Haar compatible reference energy for the actual canonical
physical profiles. Both profile construction and one-input stability are
proved, and the row is the squared sum of the actual signed Haar columns. -/
theorem canonical_reference_energy_bound
    {a : ℝ → ℝ} {ell M H β h : ℝ} (u v : CircleL2)
    (ha : Measurable a) (hell : 0 < ell) (hM : 0 ≤ M) (hH : 0 ≤ H)
    (hβ : 0 < β) (hβ1 : β ≤ 1) (hh : 0 < h) (hh1 : h ≤ 1)
    (hal : ∀ z, ell ≤ a z) (hau : ∀ z, a z ≤ M)
    (hholder : ∀ z w, |a z - a w| ≤ H * |z - w| ^ β)
    (hsmall : contractionConstant ell H β * h ^ (β / 4) ≤ 1 / 2)
    (hsmallL2 : memoryConstant ell H β * ProfileVolterra.powerConstant ((β - 1) / 4) * h ^ (β / 4) ≤ 1 / 2) :
    IntervalIntegrable (profileRow a ell h u v h) volume 0 h ∧
      (∫ s in (0 : ℝ)..h, profileRow a ell h u v h s) ≤
        referenceConstant ell M H β * h ^ (β / 2) * ‖u - v‖ ^ 2 := by
  have hm := l2Profile_measurable ha hell hM hH hβ hβ1 hh hh1 hal hau hholder hsmall
  have hreal (w : CircleL2) (s : ℝ) :=
    l2Profile_real_elliptic ha hell hM hH hβ hβ1 hh hh1 hal hau hholder hsmall (w, s)
  have he := nativeEnergy_time_bound
    (f := fun s => l2Profile a ell h (u, s)) (g := fun s => l2Profile a ell h (v, s))
    (P := 2 * meanConstant ell H β) (D := ‖u - v‖)
    (hm.comp (measurable_const.prodMk measurable_id)) (hm.comp (measurable_const.prodMk measurable_id)) hell hM
    (fun s => (hreal u s).mono (fun _ hx => hx.1))
    (fun s => (hreal v s).mono (fun _ hx => hx.1))
    (fun s => (hreal u s).mono (fun _ hx => hx.2))
    (fun s => (hreal v s).mono (fun _ hx => hx.2))
    (by linarith : -1 < β) hh hh1
    (mul_nonneg (by norm_num) (meanConstant_nonneg (β := β) hell.le hH)) (norm_nonneg _)
    (fun s hs => by
      have hb := l2Profile_stability ha hell hM hH hβ hβ1 hh hh1 hal hau hholder hsmall hsmallL2 u v s ⟨hs.1, hs.2.le⟩
      convert hb using 1; ring)
  refine ⟨he.1, ?_⟩
  convert he.2 using 1 <;> (first | rfl | (unfold referenceConstant; ring))

/-- The printed common-Haar reference pair is stable once the standard
centered stochastic-integral isometry is supplied. No profile estimate,
factor estimate, or covariance-comparison assertion is assumed. -/
theorem canonical_reference_stability_from_isometry
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {Z : Ω → CircleL2} (hZ : MemLp Z 2 μ) (hcenter : (∫ ω, Z ω ∂μ) = 0)
    {a : ℝ → ℝ} {ell M H β h : ℝ} (u v : CircleL2)
    (ha : Measurable a) (hell : 0 < ell) (hM : 0 ≤ M) (hH : 0 ≤ H)
    (hβ : 0 < β) (hβ1 : β ≤ 1) (hh : 0 < h) (hh1 : h ≤ 1)
    (hal : ∀ z, ell ≤ a z) (hau : ∀ z, a z ≤ M)
    (hholder : ∀ z w, |a z - a w| ≤ H * |z - w| ^ β)
    (hsmall : contractionConstant ell H β * h ^ (β / 4) ≤ 1 / 2)
    (hsmallL2 : memoryConstant ell H β * ProfileVolterra.powerConstant ((β - 1) / 4) * h ^ (β / 4) ≤ 1 / 2)
    (hisometry : (∫ ω, ‖Z ω‖ ^ 2 ∂μ) = ∫ s in (0 : ℝ)..h, profileRow a ell h u v h s) :
    (∫ ω, ‖Z ω‖ ^ 2 ∂μ) ≤
      referenceConstant ell M H β * h ^ (β / 2) * ‖u - v‖ ^ 2 ∧
    (∫ ω, ‖circleHeatOperator h hh.le (u - v) + Z ω‖ ^ 2 ∂μ) ≤
      (1 + referenceConstant ell M H β) * ‖u - v‖ ^ 2 := by
  have hrow := canonical_reference_energy_bound u v ha hell hM hH hβ hβ1 hh hh1 hal hau hholder hsmall hsmallL2
  have hnoise : (∫ ω, ‖Z ω‖ ^ 2 ∂μ) ≤
      referenceConstant ell M H β * h ^ (β / 2) * ‖u - v‖ ^ 2 := by
    rw [hisometry]
    exact hrow.2
  refine ⟨hnoise, ?_⟩
  exact ProfileVolterra.compatible_reference_total_bound μ hZ hcenter
    (circleHeatOperator h hh.le (u - v)) hβ.le hh hh1 (norm_nonneg _)
    (referenceConstant_nonneg hM (by linarith : -1 < β))
    (circleHeatOperator_norm_le h hh.le (u - v)) hnoise

end SHE.HaarReference
