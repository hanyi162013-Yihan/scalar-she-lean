module

public import SHE.PhysicalProfile

@[expose] public section
set_option autoImplicit false

/-! Jointly measurable canonical scalar profiles through actual Picard iterates. -/
noncomputable section
namespace SHE.ParametricProfile
open Set MeasureTheory AddCircle StoppedFourier ProfileVariance GaussianProfile
open Filter
open scoped Topology

local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
abbrev Domain := ℝ × HeatCircle

def varianceDensityFamily {X : Type*} (C : X × Domain → ℝ) (p : (X × Domain) × ℝ) : ℝ :=
  varianceDensity (fun q => C (p.1.1, q)) p.1.2.1 p.1.2.2 p.2

def positiveVarianceFamily {X : Type*} (C : X × Domain → ℝ) (p : X × Domain) : ℝ :=
  positiveVarianceMap (fun q => C (p.1, q)) p.2

theorem varianceDensityFamily_measurable {X : Type*} [MeasurableSpace X]
    {C : X × Domain → ℝ} (hC : Measurable C) : Measurable (varianceDensityFamily C) := by
  have hmapK : Measurable (fun p : ((X × Domain) × ℝ) × HeatCircle =>
      ((p.1.1.2.1 - p.1.2, p.1.1.2.2), p.2)) := by fun_prop
  have hmapC : Measurable (fun p : ((X × Domain) × ℝ) × HeatCircle =>
      (p.1.1.1, (p.1.2, p.2))) := by fun_prop
  have hK := heatPhysical_joint_measurable.comp hmapK
  have hC' := hC.comp hmapC
  have hm := (((hK.norm.pow_const (2 : ℕ)).mul hC').stronglyMeasurable.integral_prod_right'
    (ν := haarAddCircle)).measurable
  exact hm

theorem positiveVarianceFamily_measurable {X : Type*} [MeasurableSpace X]
    {C : X × Domain → ℝ} (hC : Measurable C) : Measurable (positiveVarianceFamily C) := by
  classical
  have hset : MeasurableSet {p : (X × Domain) × ℝ | 0 < p.2 ∧ p.2 ≤ p.1.2.1} := by
    exact (measurableSet_lt measurable_const measurable_snd).inter
      (measurableSet_le measurable_snd measurable_fst.snd.fst)
  have hm : Measurable (fun p : (X × Domain) × ℝ =>
      if 0 < p.2 ∧ p.2 ≤ p.1.2.1 then varianceDensityFamily C p else 0) :=
    (varianceDensityFamily_measurable hC).ite hset measurable_const
  exact (hm.stronglyMeasurable.integral_prod_right' (ν := volume)).measurable

def update {X : Type*} (a : ℝ → ℝ) (Φ C : X × Domain → ℝ) (ell h : ℝ) (p : X × Domain) : ℝ :=
  if p.2.1 ∈ Ioc 0 h then gaussianAverage a (Φ p) (positiveVarianceFamily C p) else ell

theorem update_measurable {X : Type*} [MeasurableSpace X] {a : ℝ → ℝ}
    {Φ C : X × Domain → ℝ} (ha : Measurable a) (hΦ : Measurable Φ) (hC : Measurable C)
    (ell h : ℝ) : Measurable (update a Φ C ell h) := by
  classical
  have hm := (gaussianAverage_joint_measurable ha).comp
    (hΦ.prodMk (positiveVarianceFamily_measurable hC))
  exact hm.ite (measurableSet_Ioc.preimage measurable_snd.fst) measurable_const

def picard {X : Type*} (a : ℝ → ℝ) (Φ : X × Domain → ℝ) (ell h : ℝ) : ℕ → X × Domain → ℝ
  | 0 => fun _ => ell
  | n + 1 => update a Φ (picard a Φ ell h n) ell h

theorem picard_measurable {X : Type*} [MeasurableSpace X] {a : ℝ → ℝ}
    {Φ : X × Domain → ℝ} (ha : Measurable a) (hΦ : Measurable Φ) (ell h : ℝ) (n : ℕ) :
    Measurable (picard a Φ ell h n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih => exact update_measurable ha hΦ ih ell h

theorem picard_elliptic {X : Type*} {a : ℝ → ℝ} {Φ : X × Domain → ℝ} {ell M h : ℝ}
    (ha : Measurable a) (hell : 0 ≤ ell) (hM : 0 ≤ M)
    (hal : ∀ z, ell ≤ a z) (hau : ∀ z, a z ≤ M) (n : ℕ) (p : X × Domain) :
    ell ≤ picard a Φ ell h n p ∧ picard a Φ ell h n p ≤ M := by
  cases n with
  | zero => exact ⟨le_rfl, (hal 0).trans (hau 0)⟩
  | succ n =>
    simp only [picard, update]
    split_ifs
    · exact gaussianAverage_elliptic ha hell hM hal hau _ _
    · exact ⟨le_rfl, (hal 0).trans (hau 0)⟩

def canonicalProfile {X : Type*} (a : ℝ → ℝ) (Φ : X × Domain → ℝ) (ell h : ℝ)
    (p : X × Domain) : ℝ :=
  atTop.limUnder (fun n : ℕ => picard a Φ ell h n p)

theorem picard_error {X : Type*} [MeasurableSpace X] {a : ℝ → ℝ}
    {Φ : X × Domain → ℝ} {ell M H β h : ℝ}
    (ha : Measurable a) (hΦ : Measurable Φ) (hell : 0 < ell) (hM : 0 ≤ M)
    (hH : 0 ≤ H) (hβ : 0 < β) (hβ1 : β ≤ 1) (_hh : 0 < h) (hh1 : h ≤ 1)
    (hal : ∀ z, ell ≤ a z) (hau : ∀ z, a z ≤ M)
    (hholder : ∀ z w, |a z - a w| ≤ H * |z - w| ^ β)
    (hsmall : contractionConstant ell H β * h ^ (β / 4) ≤ 1 / 2)
    (u : X) (c : Domain → ℝ) (hc : Measurable c) (hcb : ∀ p, ell ≤ c p ∧ c p ≤ M)
    (hcf : ∀ r ∈ Ioc 0 h, ∀ x, c (r, x) = profileUpdate a (fun q => Φ (u, q)) c r x)
    (n : ℕ) (p : Domain) :
    |picard a Φ ell h n (u, p) - (if p.1 ∈ Ioc 0 h then c p else ell)| ≤
      M * (1 / 2 : ℝ) ^ n := by
  classical
  have haB : ∀ z, |a z| ≤ M := by
    intro z
    rw [abs_of_nonneg (hell.le.trans (hal z))]
    exact hau z
  induction n generalizing p with
  | zero =>
    simp only [picard, pow_zero, mul_one]
    split_ifs
    · rw [abs_le]
      constructor <;> linarith [(hcb p).1, (hcb p).2]
    · simpa using hM
  | succ n ih =>
    by_cases hp : p.1 ∈ Ioc 0 h
    · simp only [picard, update, ite_eq_left hp]
      rw [positiveVarianceFamily, positiveVarianceMap_eq hp.1.le]
      change |profileUpdate a (fun q => Φ (u, q)) (fun q => picard a Φ ell h n (u, q)) p.1 p.2 - c p| ≤ _
      rw [hcf p.1 hp p.2]
      have hn : 0 ≤ M * (1 / 2 : ℝ) ^ n := by positivity
      have hcn : Measurable (fun q => picard a Φ ell h n (u, q)) :=
        (picard_measurable ha hΦ ell h n).comp (measurable_const.prodMk measurable_id)
      have he := profileUpdate_contraction (φ := fun q => Φ (u, q)) ha hcn hc hp.1 (hp.2.trans hh1) hell hM hH hβ.le
        (by linarith : β ≤ 2) hn haB hholder
        (fun s _ y => (picard_elliptic ha hell.le hM hal hau n (u, (s, y))).1)
        (fun s _ y => (picard_elliptic ha hell.le hM hal hau n (u, (s, y))).2)
        (fun s _ y => (hcb (s, y)).1) (fun s _ y => (hcb (s, y)).2)
        (fun s hs y => by
          have hsp : s ∈ Ioc 0 h := ⟨hs.1, hs.2.le.trans hp.2⟩
          simpa only [ite_eq_left hsp] using ih (s, y)) p.2
      have hq : contractionConstant ell H β * p.1 ^ (β / 4) ≤ 1 / 2 := by
        apply le_trans _ hsmall
        exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hp.1.le hp.2 (by positivity))
          (contractionConstant_nonneg hell.le hH)
      calc
        _ ≤ _ := he
        _ ≤ (1 / 2 : ℝ) * (M * (1 / 2 : ℝ) ^ n) := mul_le_mul_of_nonneg_right hq hn
        _ = _ := by rw [pow_succ]; ring
    · simp only [picard, update, ite_eq_right hp, sub_self, abs_zero]
      positivity

theorem picard_tendsto_clipped {X : Type*} [MeasurableSpace X] {a : ℝ → ℝ}
    {Φ : X × Domain → ℝ} {ell M H β h : ℝ}
    (ha : Measurable a) (hΦ : Measurable Φ) (hell : 0 < ell) (hM : 0 ≤ M)
    (hH : 0 ≤ H) (hβ : 0 < β) (hβ1 : β ≤ 1) (hh : 0 < h) (hh1 : h ≤ 1)
    (hal : ∀ z, ell ≤ a z) (hau : ∀ z, a z ≤ M)
    (hholder : ∀ z w, |a z - a w| ≤ H * |z - w| ^ β)
    (hsmall : contractionConstant ell H β * h ^ (β / 4) ≤ 1 / 2)
    (u : X) (c : Domain → ℝ) (hc : Measurable c) (hcb : ∀ p, ell ≤ c p ∧ c p ≤ M)
    (hcf : ∀ r ∈ Ioc 0 h, ∀ x, c (r, x) = profileUpdate a (fun q => Φ (u, q)) c r x)
    (p : Domain) : Tendsto (fun n : ℕ => picard a Φ ell h n (u, p)) atTop
      (𝓝 (if p.1 ∈ Ioc 0 h then c p else ell)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have he := squeeze_zero (fun n => abs_nonneg (picard a Φ ell h n (u, p) -
      (if p.1 ∈ Ioc 0 h then c p else ell)))
    (fun n => picard_error ha hΦ hell hM hH hβ hβ1 hh hh1 hal hau hholder hsmall u c hc hcb hcf n p)
    (by simpa only [mul_zero] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num : (1 / 2 : ℝ) < 1)).const_mul M)
  simpa only [Real.norm_eq_abs] using he

theorem canonicalProfile_eq_clipped {X : Type*} [MeasurableSpace X] {a : ℝ → ℝ}
    {Φ : X × Domain → ℝ} {ell M H β h : ℝ}
    (ha : Measurable a) (hΦ : Measurable Φ) (hell : 0 < ell) (hM : 0 ≤ M)
    (hH : 0 ≤ H) (hβ : 0 < β) (hβ1 : β ≤ 1) (hh : 0 < h) (hh1 : h ≤ 1)
    (hal : ∀ z, ell ≤ a z) (hau : ∀ z, a z ≤ M)
    (hholder : ∀ z w, |a z - a w| ≤ H * |z - w| ^ β)
    (hsmall : contractionConstant ell H β * h ^ (β / 4) ≤ 1 / 2)
    (u : X) (c : Domain → ℝ) (hc : Measurable c) (hcb : ∀ p, ell ≤ c p ∧ c p ≤ M)
    (hcf : ∀ r ∈ Ioc 0 h, ∀ x, c (r, x) = profileUpdate a (fun q => Φ (u, q)) c r x)
    (p : Domain) : canonicalProfile a Φ ell h (u, p) = if p.1 ∈ Ioc 0 h then c p else ell :=
  (picard_tendsto_clipped ha hΦ hell hM hH hβ hβ1 hh hh1 hal hau hholder hsmall u c hc hcb hcf p).limUnder_eq

theorem picard_tendsto_canonical {X : Type*} [MeasurableSpace X] {a : ℝ → ℝ}
    {Φ : X × Domain → ℝ} {ell M H β h : ℝ}
    (ha : Measurable a) (hΦ : Measurable Φ) (hell : 0 < ell) (hM : 0 ≤ M)
    (hH : 0 ≤ H) (hβ : 0 < β) (hβ1 : β ≤ 1) (hh : 0 < h) (hh1 : h ≤ 1)
    (hal : ∀ z, ell ≤ a z) (hau : ∀ z, a z ≤ M)
    (hholder : ∀ z w, |a z - a w| ≤ H * |z - w| ^ β)
    (hsmall : contractionConstant ell H β * h ^ (β / 4) ≤ 1 / 2) (p : X × Domain) :
    Tendsto (fun n : ℕ => picard a Φ ell h n p) atTop (𝓝 (canonicalProfile a Φ ell h p)) := by
  obtain ⟨c, hc, hcb, hcf⟩ := ScalarProfileFixedPoint.exists_scalar_profile ha
    (hΦ.comp (measurable_const.prodMk measurable_id)) hell hM hH hβ hβ1 hh hh1 hal hau hholder hsmall
  have he := picard_tendsto_clipped ha hΦ hell hM hH hβ hβ1 hh hh1 hal hau hholder hsmall
    p.1 c hc hcb hcf p.2
  exact tendsto_nhds_limUnder ⟨_, he⟩

/-- The canonical limit of the actual Picard scheme is jointly measurable
in an arbitrary measurable input parameter, time, and physical center. -/
theorem canonicalProfile_measurable {X : Type*} [MeasurableSpace X] {a : ℝ → ℝ}
    {Φ : X × Domain → ℝ} {ell M H β h : ℝ}
    (ha : Measurable a) (hΦ : Measurable Φ) (hell : 0 < ell) (hM : 0 ≤ M)
    (hH : 0 ≤ H) (hβ : 0 < β) (hβ1 : β ≤ 1) (hh : 0 < h) (hh1 : h ≤ 1)
    (hal : ∀ z, ell ≤ a z) (hau : ∀ z, a z ≤ M)
    (hholder : ∀ z w, |a z - a w| ≤ H * |z - w| ^ β)
    (hsmall : contractionConstant ell H β * h ^ (β / 4) ≤ 1 / 2) :
    Measurable (canonicalProfile a Φ ell h) := by
  apply measurable_of_tendsto_metrizable (fun n => picard_measurable ha hΦ ell h n)
  exact tendsto_pi_nhds.mpr (picard_tendsto_canonical ha hΦ hell hM hH hβ hβ1 hh hh1 hal hau hholder hsmall)

theorem canonicalProfile_elliptic {X : Type*} [MeasurableSpace X] {a : ℝ → ℝ}
    {Φ : X × Domain → ℝ} {ell M H β h : ℝ}
    (ha : Measurable a) (hΦ : Measurable Φ) (hell : 0 < ell) (hM : 0 ≤ M)
    (hH : 0 ≤ H) (hβ : 0 < β) (hβ1 : β ≤ 1) (hh : 0 < h) (hh1 : h ≤ 1)
    (hal : ∀ z, ell ≤ a z) (hau : ∀ z, a z ≤ M)
    (hholder : ∀ z w, |a z - a w| ≤ H * |z - w| ^ β)
    (hsmall : contractionConstant ell H β * h ^ (β / 4) ≤ 1 / 2) (p : X × Domain) :
    ell ≤ canonicalProfile a Φ ell h p ∧ canonicalProfile a Φ ell h p ≤ M := by
  apply isClosed_Icc.mem_of_tendsto
    (picard_tendsto_canonical ha hΦ hell hM hH hβ hβ1 hh hh1 hal hau hholder hsmall p)
  exact Eventually.of_forall (fun n => picard_elliptic ha hell.le hM hal hau n p)

theorem varianceMap_congr_Ioo {c d : Domain → ℝ} {r : ℝ} (hr : 0 ≤ r)
    (hcd : ∀ s ∈ Ioo 0 r, ∀ y, c (s, y) = d (s, y)) (x : HeatCircle) :
    varianceMap c r x = varianceMap d r x := by
  unfold varianceMap
  apply intervalIntegral.integral_congr_ae_restrict
  rw [uIoc_of_le hr]
  filter_upwards [ae_restrict_mem measurableSet_Ioc,
    ae_restrict_of_ae (volume.ae_ne r)] with s hs hsr
  have hs' : s ∈ Ioo 0 r := ⟨hs.1, lt_of_le_of_ne hs.2 hsr⟩
  unfold varianceDensity
  apply integral_congr_ae
  filter_upwards with y
  rw [hcd s hs' y]

/-- The jointly measurable Picard limit satisfies the genuine nonlinear
profile equation at every physical time and center. -/
theorem canonicalProfile_fixed {X : Type*} [MeasurableSpace X] {a : ℝ → ℝ}
    {Φ : X × Domain → ℝ} {ell M H β h : ℝ}
    (ha : Measurable a) (hΦ : Measurable Φ) (hell : 0 < ell) (hM : 0 ≤ M)
    (hH : 0 ≤ H) (hβ : 0 < β) (hβ1 : β ≤ 1) (hh : 0 < h) (hh1 : h ≤ 1)
    (hal : ∀ z, ell ≤ a z) (hau : ∀ z, a z ≤ M)
    (hholder : ∀ z w, |a z - a w| ≤ H * |z - w| ^ β)
    (hsmall : contractionConstant ell H β * h ^ (β / 4) ≤ 1 / 2)
    (u : X) (r : ℝ) (hr : r ∈ Ioc 0 h) (x : HeatCircle) :
    canonicalProfile a Φ ell h (u, (r, x)) =
      profileUpdate a (fun q => Φ (u, q)) (fun q => canonicalProfile a Φ ell h (u, q)) r x := by
  obtain ⟨c, hc, hcb, hcf⟩ := ScalarProfileFixedPoint.exists_scalar_profile ha
    (hΦ.comp (measurable_const.prodMk measurable_id)) hell hM hH hβ hβ1 hh hh1 hal hau hholder hsmall
  have heq := canonicalProfile_eq_clipped ha hΦ hell hM hH hβ hβ1 hh hh1 hal hau hholder hsmall u c hc hcb hcf
  have hV : varianceMap (fun q => canonicalProfile a Φ ell h (u, q)) r x = varianceMap c r x := by
    apply varianceMap_congr_Ioo hr.1.le
    intro s hs y
    have hsH : s ∈ Ioc 0 h := ⟨hs.1, hs.2.le.trans hr.2⟩
    simpa only [ite_eq_left hsH] using heq (s, y)
  rw [heq (r, x), ite_eq_left hr, hcf r hr x]
  unfold profileUpdate
  rw [hV]
  rfl

/-- Uniform geometric error for the canonical measurable realization. -/
theorem canonicalProfile_picard_error {X : Type*} [MeasurableSpace X] {a : ℝ → ℝ}
    {Φ : X × Domain → ℝ} {ell M H β h : ℝ}
    (ha : Measurable a) (hΦ : Measurable Φ) (hell : 0 < ell) (hM : 0 ≤ M)
    (hH : 0 ≤ H) (hβ : 0 < β) (hβ1 : β ≤ 1) (hh : 0 < h) (hh1 : h ≤ 1)
    (hal : ∀ z, ell ≤ a z) (hau : ∀ z, a z ≤ M)
    (hholder : ∀ z w, |a z - a w| ≤ H * |z - w| ^ β)
    (hsmall : contractionConstant ell H β * h ^ (β / 4) ≤ 1 / 2) (n : ℕ) (p : X × Domain) :
    |picard a Φ ell h n p - canonicalProfile a Φ ell h p| ≤ M * (1 / 2 : ℝ) ^ n := by
  obtain ⟨c, hc, hcb, hcf⟩ := ScalarProfileFixedPoint.exists_scalar_profile ha
    (hΦ.comp (measurable_const.prodMk measurable_id)) hell hM hH hβ hβ1 hh hh1 hal hau hholder hsmall
  rw [canonicalProfile_eq_clipped ha hΦ hell hM hH hβ hβ1 hh hh1 hal hau hholder hsmall p.1 c hc hcb hcf p.2]
  exact picard_error ha hΦ hell hM hH hβ hβ1 hh hh1 hal hau hholder hsmall p.1 c hc hcb hcf n p.2

theorem picard_comap {X Y : Type*} (a : ℝ → ℝ) (Φ : X × Domain → ℝ) (ell h : ℝ)
    (f : Y → X) (n : ℕ) (p : Y × Domain) :
    picard a (fun q => Φ (f q.1, q.2)) ell h n p = picard a Φ ell h n (f p.1, p.2) := by
  induction n generalizing p with
  | zero => rfl
  | succ n ih =>
    simp only [picard, update, positiveVarianceFamily]
    have he : (fun q => picard a (fun z => Φ (f z.1, z.2)) ell h n (p.1, q)) =
        fun q => picard a Φ ell h n (f p.1, q) := funext (fun q => ih (p.1, q))
    rw [he]

/-- Exact compatibility with arbitrary input substitution follows directly
from the actual iterates, so no measurable-selection ambiguity remains. -/
theorem canonicalProfile_comap {X Y : Type*} (a : ℝ → ℝ) (Φ : X × Domain → ℝ) (ell h : ℝ)
    (f : Y → X) (p : Y × Domain) :
    canonicalProfile a (fun q => Φ (f q.1, q.2)) ell h p = canonicalProfile a Φ ell h (f p.1, p.2) := by
  unfold canonicalProfile
  congr 1
  funext n
  exact picard_comap a Φ ell h f n p

end SHE.ParametricProfile
