module

public import SHE.GaussianProfile
public import SHE.GaussianProfileMean
public import SHE.ProfileVolterra

@[expose] public section
set_option autoImplicit false

/-! Actual spatial L² transfer for the heat-square variance map. -/
noncomputable section
namespace SHE.ProfileL2
open Set MeasureTheory AddCircle StoppedFourier ProfileVariance GaussianProfile

def normTwo {X : Type*} [MeasurableSpace X] (μ : Measure X) (f : X → ℝ) : ℝ :=
  Real.sqrt (∫ x, f x ^ 2 ∂μ)

theorem normTwo_nonneg {X : Type*} [MeasurableSpace X] (μ : Measure X) (f : X → ℝ) :
    0 ≤ normTwo μ f := Real.sqrt_nonneg _

theorem normTwo_sq {X : Type*} [MeasurableSpace X] (μ : Measure X) (f : X → ℝ) :
    normTwo μ f ^ 2 = ∫ x, f x ^ 2 ∂μ :=
  Real.sq_sqrt (integral_nonneg (fun _ => sq_nonneg _))

theorem normTwo_eq_toLp {X : Type*} [MeasurableSpace X] {μ : Measure X} {f : X → ℝ}
    (hf : MemLp f 2 μ) : normTwo μ f = ‖hf.toLp f‖ := by
  have hsq : ‖hf.toLp f‖ ^ 2 = ∫ x, f x ^ 2 ∂μ := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hf.coeFn_toLp] with x hx
    simp only [hx, real_inner_self_eq_norm_sq, Real.norm_eq_abs, sq_abs]
  rw [normTwo, ← hsq, Real.sqrt_sq (norm_nonneg _)]

theorem integral_mul_normTwo_bound {X : Type*} [MeasurableSpace X]
    {μ : Measure X} {f g : X → ℝ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    |∫ x, f x * g x ∂μ| ≤ normTwo μ f * normTwo μ g := by
  have he : inner ℝ (hf.toLp f) (hg.toLp g) = ∫ x, f x * g x ∂μ := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with x hx hy
    simp only [hx, hy, RCLike.inner_apply, conj_trivial, mul_comm]
  rw [normTwo_eq_toLp hf, normTwo_eq_toLp hg, ← he]
  simpa only [Real.norm_eq_abs] using norm_inner_le_norm (𝕜 := ℝ) (hf.toLp f) (hg.toLp g)

theorem bounded_memLp {X : Type*} [MeasurableSpace X] {μ : Measure X}
    [IsFiniteMeasure μ] {f : X → ℝ} (hf : Measurable f) {C : ℝ}
    (hb : ∀ x, |f x| ≤ C) : MemLp f 2 μ :=
  MemLp.of_bound hf.aestronglyMeasurable C (ae_of_all _ hb)

theorem normTwo_bound {X : Type*} [MeasurableSpace X] {μ : Measure X}
    [IsProbabilityMeasure μ] {f : X → ℝ} (hf : Measurable f) {C : ℝ}
    (hC : 0 ≤ C) (hb : ∀ x, |f x| ≤ C) : normTwo μ f ≤ C := by
  have hi := (bounded_memLp (μ := μ) hf hb).integrable_sq
  have he : (∫ x, f x ^ 2 ∂μ) ≤ C ^ 2 := by
    calc
      _ ≤ ∫ _ : X, C ^ 2 ∂μ := by
        apply integral_mono hi (integrable_const _)
        intro x
        simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hC).mpr (hb x)
      _ = _ := by simp
  have hs := normTwo_sq μ f
  nlinarith [normTwo_nonneg μ f]

theorem normTwo_mono {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {f g : X → ℝ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ)
    (hfg : ∀ᵐ x ∂μ, |f x| ≤ |g x|) : normTwo μ f ≤ normTwo μ g := by
  apply Real.sqrt_le_sqrt
  apply integral_mono_ae hf.integrable_sq hg.integrable_sq
  filter_upwards [hfg] with x hx
  simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) (abs_nonneg _)).mpr hx

theorem normTwo_add {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {f g : X → ℝ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    normTwo μ (f + g) ≤ normTwo μ f + normTwo μ g := by
  rw [normTwo_eq_toLp (hf.add hg), normTwo_eq_toLp hf, normTwo_eq_toLp hg,
    MemLp.toLp_add hf hg]
  exact norm_add_le _ _

theorem normTwo_const_mul {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {f : X → ℝ} (hf : MemLp f 2 μ) (C : ℝ) :
    normTwo μ (fun x => C * f x) = |C| * normTwo μ f := by
  rw [normTwo_eq_toLp (hf.const_mul C), normTwo_eq_toLp hf]
  have he : (hf.const_mul C).toLp (fun x => C * f x) = C • hf.toLp f := by
    apply Lp.ext
    filter_upwards [(hf.const_mul C).coeFn_toLp, hf.coeFn_toLp,
      Lp.coeFn_smul C (hf.toLp f)] with x hx hy hz
    rw [hx, hz, Pi.smul_apply, smul_eq_mul, hy]
  rw [he, norm_smul, Real.norm_eq_abs]

/-- Minkowski's integral inequality for actual bounded scalar spatial fields.
Only a scalar integrable envelope is used to justify Fubini; the conclusion
retains the integral of the section L² bounds. -/
theorem bounded_minkowski_two {A X : Type*} [MeasurableSpace A] [MeasurableSpace X]
    {μ : Measure A} {ν : Measure X} [SFinite μ] [IsProbabilityMeasure ν]
    {F : A × X → ℝ} {a b : A → ℝ}
    (hF : Measurable F) (ha : Integrable a μ) (hb : Integrable b μ)
    (ha0 : 0 ≤ᵐ[μ] a) (hb0 : 0 ≤ᵐ[μ] b)
    (hFb : ∀ᵐ s ∂μ, ∀ x, |F (s, x)| ≤ b s)
    (hFa : ∀ᵐ s ∂μ, normTwo ν (fun x => F (s, x)) ≤ a s) :
    normTwo ν (fun x => ∫ s, F (s, x) ∂μ) ≤ ∫ s, a s ∂μ := by
  let g : X → ℝ := fun x => ∫ s, F (s, x) ∂μ
  let B : ℝ := ∫ s, b s ∂μ
  have hB : 0 ≤ B := integral_nonneg_of_ae hb0
  have hg : Measurable g := hF.stronglyMeasurable.integral_prod_left'.measurable
  have hgB : ∀ x, |g x| ≤ B := by
    intro x
    simpa only [Real.norm_eq_abs] using
      (norm_integral_le_of_norm_le (f := fun s => F (s, x)) hb
        (hFb.mono (fun s hs => by simpa only [Real.norm_eq_abs] using hs x)))
  have hgm : MemLp g 2 ν := bounded_memLp hg hgB
  have hprod : Integrable (fun p : A × X => g p.2 * F p) (μ.prod ν) := by
    apply ((hb.const_mul B).comp_fst ν).mono'
    · exact ((hg.comp measurable_snd).mul hF).aestronglyMeasurable
    · filter_upwards [Measure.quasiMeasurePreserving_fst.ae hFb] with p hp
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul (hgB p.2) (hp p.2) (abs_nonneg _) hB
  have henergy : (∫ x, g x ^ 2 ∂ν) = ∫ s, ∫ x, g x * F (s, x) ∂ν ∂μ := by
    rw [integral_integral_swap hprod]
    apply integral_congr_ae
    filter_upwards with x
    rw [integral_const_mul]
    change g x ^ 2 = g x * g x
    ring
  have hi : Integrable (fun s => ∫ x, g x * F (s, x) ∂ν) μ := hprod.integral_prod_left
  have he : (∫ x, g x ^ 2 ∂ν) ≤ normTwo ν g * ∫ s, a s ∂μ := by
    rw [henergy, ← integral_const_mul]
    apply integral_mono_ae hi (ha.const_mul _)
    filter_upwards [hFb, hFa] with s hsb hsa
    have hsm : MemLp (fun x => F (s, x)) 2 ν :=
      bounded_memLp (hF.comp (measurable_const.prodMk measurable_id)) hsb
    calc
      _ ≤ |∫ x, g x * F (s, x) ∂ν| := le_abs_self _
      _ ≤ normTwo ν g * normTwo ν (fun x => F (s, x)) := integral_mul_normTwo_bound hgm hsm
      _ ≤ _ := mul_le_mul_of_nonneg_left hsa (normTwo_nonneg _ _)
  have hs := normTwo_sq ν g
  have hI : 0 ≤ ∫ s, a s ∂μ := integral_nonneg_of_ae ha0
  change normTwo ν g ≤ _
  nlinarith [normTwo_nonneg ν g]

/-- The genuine L² Schur estimate for a bounded symmetric positive kernel
with constant row mass. Both integrations and the Cauchy--Schwarz step are
performed on the actual scalar fields. -/
theorem bounded_symmetric_schur_two {X : Type*} [MeasurableSpace X] [Nonempty X]
    {ν : Measure X} [IsProbabilityMeasure ν] {K : X × X → ℝ} {f : X → ℝ}
    {B C k : ℝ} (hK : Measurable K) (hf : Measurable f)
    (hB : 0 ≤ B) (hC : 0 ≤ C) (hK0 : ∀ x y, 0 ≤ K (x, y))
    (hKB : ∀ x y, K (x, y) ≤ B) (hfC : ∀ x, |f x| ≤ C)
    (hsymm : ∀ x y, K (x, y) = K (y, x))
    (hmass : ∀ x, (∫ y, K (x, y) ∂ν) = k) :
    normTwo ν (fun x => ∫ y, K (x, y) * f y ∂ν) ≤ k * normTwo ν f := by
  let T : X → ℝ := fun x => ∫ y, K (x, y) * f y ∂ν
  have hki (x : X) : Integrable (fun y => K (x, y)) ν := by
    apply (bounded_memLp (μ := ν) (f := fun y => K (x, y))
      (hK.comp (measurable_const.prodMk measurable_id))
      (fun y => by rw [abs_of_nonneg (hK0 x y)]; exact hKB x y)).integrable (by norm_num)
  have hk : 0 ≤ k := by
    exact (hmass (Classical.arbitrary X)) ▸ integral_nonneg (hK0 _)
  have hTm : Measurable T :=
    (hK.mul (hf.comp measurable_snd)).stronglyMeasurable.integral_prod_right'.measurable
  have hTb : ∀ x, |T x| ≤ k * C := by
    intro x
    have hb : ∀ y, ‖K (x, y) * f y‖ ≤ K (x, y) * C := by
      intro y
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hK0 x y)]
      exact mul_le_mul_of_nonneg_left (hfC y) (hK0 x y)
    have he := norm_integral_le_of_norm_le ((hki x).mul_const C) (ae_of_all _ hb)
    simpa only [Real.norm_eq_abs, integral_mul_const, hmass] using he
  have hTmem := bounded_memLp (μ := ν) hTm hTb
  have hpoint : ∀ x, T x ^ 2 ≤ k * ∫ y, K (x, y) * f y ^ 2 ∂ν := by
    intro x
    let P : X → ℝ := fun y => Real.sqrt (K (x, y))
    let Q : X → ℝ := fun y => P y * f y
    have hPm : Measurable P := (hK.comp (measurable_const.prodMk measurable_id)).sqrt
    have hPb : ∀ y, |P y| ≤ Real.sqrt B := by
      intro y
      rw [abs_of_nonneg (Real.sqrt_nonneg _)]
      exact Real.sqrt_le_sqrt (hKB x y)
    have hQb : ∀ y, |Q y| ≤ Real.sqrt B * C := by
      intro y
      rw [abs_mul]
      exact mul_le_mul (hPb y) (hfC y) (abs_nonneg _) (Real.sqrt_nonneg _)
    have hPmL := bounded_memLp (μ := ν) hPm hPb
    have hQmL : MemLp Q 2 ν := bounded_memLp (μ := ν) (hPm.mul hf) hQb
    have hP2 : normTwo ν P ^ 2 = k := by
      rw [normTwo_sq]
      have he : (fun y => P y ^ 2) = fun y => K (x, y) := by
        funext y
        exact Real.sq_sqrt (hK0 x y)
      rw [he, hmass]
    have hQ2 : normTwo ν Q ^ 2 = ∫ y, K (x, y) * f y ^ 2 ∂ν := by
      rw [normTwo_sq]
      apply integral_congr_ae
      filter_upwards with y
      dsimp only [Q, P]
      rw [mul_pow, Real.sq_sqrt (hK0 x y)]
    have heq : (∫ y, P y * Q y ∂ν) = T x := by
      apply integral_congr_ae
      filter_upwards with y
      dsimp only [P, Q]
      rw [← mul_assoc, ← pow_two, Real.sq_sqrt (hK0 x y)]
    have he := integral_mul_normTwo_bound hPmL hQmL
    rw [heq] at he
    have hs := (sq_le_sq₀ (abs_nonneg (T x))
      (mul_nonneg (normTwo_nonneg ν P) (normTwo_nonneg ν Q))).mpr he
    simpa only [sq_abs, mul_pow, hP2, hQ2] using hs
  have hweighted : Integrable (fun p : X × X => K p * f p.2 ^ 2) (ν.prod ν) := by
    apply (integrable_const (B * C ^ 2)).mono'
    · exact (hK.mul ((hf.comp measurable_snd).pow_const (2 : ℕ))).aestronglyMeasurable
    · filter_upwards with p
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hK0 _ _) (sq_nonneg _))]
      apply mul_le_mul (hKB _ _) _ (sq_nonneg _) hB
      simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hC).mpr (hfC p.2)
  have hweighted_mass : (∫ x, ∫ y, K (x, y) * f y ^ 2 ∂ν ∂ν) =
      k * ∫ y, f y ^ 2 ∂ν := by
    rw [integral_integral_swap hweighted]
    simp_rw [integral_mul_const]
    have hc (y : X) : (∫ x, K (x, y) ∂ν) = k := by
      simpa only [hsymm] using hmass y
    simp_rw [hc]
    rw [integral_const_mul]
  have henergy : (∫ x, T x ^ 2 ∂ν) ≤ k ^ 2 * ∫ y, f y ^ 2 ∂ν := by
    calc
      _ ≤ ∫ x, k * ∫ y, K (x, y) * f y ^ 2 ∂ν ∂ν :=
        integral_mono hTmem.integrable_sq (hweighted.integral_prod_left.const_mul k) hpoint
      _ = _ := by rw [integral_const_mul, hweighted_mass]; ring
  have hsT := normTwo_sq ν T
  have hsf := normTwo_sq ν f
  have hpos := normTwo_nonneg ν T
  have hrhs : 0 ≤ k * normTwo ν f := mul_nonneg hk (normTwo_nonneg _ _)
  change normTwo ν T ≤ _
  nlinarith

local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

theorem heatPhysical_norm_symm {t : ℝ} (ht : 0 < t) (x y : HeatCircle) :
    ‖heatPhysical t x y‖ = ‖heatPhysical t y x‖ := by
  have hh : 0 < t / 2 := by positivity
  have hxy := circleHeat_cross_gram hh hh x y
  have hyx := circleHeat_cross_gram hh hh y x
  simp only [show t / 2 + t / 2 = t by ring] at hxy hyx
  simp only [heatPhysical]
  rw [← hyx, ← hxy]
  exact norm_inner_symm _ _

theorem heatPhysical_square_uniform_bound {t : ℝ} (ht : 0 < t) (x y : HeatCircle) :
    ‖heatPhysical t x y‖ ^ 2 ≤ ‖circleHeat (t / 2) (0 : HeatCircle)‖ ^ 4 := by
  have hh : 0 < t / 2 := by positivity
  have he := circleHeat_cross_gram hh hh y x
  simp only [show t / 2 + t / 2 = t by ring] at he
  have hc (z : HeatCircle) : ‖circleHeat (t / 2) z‖ = ‖circleHeat (t / 2) (0 : HeatCircle)‖ :=
    (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp (circleHeat_norm_sq_center _ z 0)
  have hn := norm_inner_le_norm (𝕜 := ℂ) (circleHeat (t / 2) y) (circleHeat (t / 2) x)
  rw [he, hc x, hc y] at hn
  have hs := (sq_le_sq₀ (norm_nonneg (heatCrossKernel t y x)) (mul_nonneg
    (norm_nonneg (circleHeat (t / 2) (0 : HeatCircle))) (norm_nonneg _))).mpr hn
  change ‖heatCrossKernel t y x‖ ^ 2 ≤ _
  convert hs using 1; ring

/-- Young's inequality for the actual positive heat-square spatial kernel.
The multiplier is its exact spatial mass, not an assumed operator bound. -/
theorem heat_square_young_two {t C : ℝ} {f : HeatCircle → ℝ}
    (ht : 0 < t) (hf : Measurable f) (hC : 0 ≤ C) (hfC : ∀ y, |f y| ≤ C) :
    normTwo haarAddCircle (fun x => ∫ y, ‖heatPhysical t x y‖ ^ 2 * f y ∂haarAddCircle) ≤
      ‖circleHeat t (0 : HeatCircle)‖ ^ 2 * normTwo haarAddCircle f := by
  have hm : Measurable (fun p : HeatCircle × HeatCircle => ‖heatPhysical t p.1 p.2‖ ^ 2) :=
    (heatPhysical_joint_measurable.comp
      ((measurable_const.prodMk measurable_fst).prodMk measurable_snd)).norm.pow_const (2 : ℕ)
  apply bounded_symmetric_schur_two hm hf (by positivity) hC
    (fun _ _ => sq_nonneg _) (heatPhysical_square_uniform_bound ht) hfC
    (fun x y => by rw [heatPhysical_norm_symm ht x y])
  intro x
  rw [heatPhysical_square_mass ht, circleHeat_norm_sq_center t x 0]

theorem varianceDensity_normTwo_le {c : ℝ × HeatCircle → ℝ} {r s C : ℝ}
    (hc : Measurable c) (hs : s < r) (hC : 0 ≤ C) (hb : ∀ y, |c (s, y)| ≤ C) :
    normTwo haarAddCircle (fun x => varianceDensity c r x s) ≤
      ‖circleHeat (r - s) (0 : HeatCircle)‖ ^ 2 *
        normTwo haarAddCircle (fun y => c (s, y)) := by
  exact heat_square_young_two (sub_pos.mpr hs)
    (hc.comp (measurable_const.prodMk measurable_id)) hC hb

theorem varianceDensity_normTwo_small_time {c : ℝ × HeatCircle → ℝ} {r s C : ℝ}
    (hc : Measurable c) (hs : s < r) (hrs : r - s ≤ 1)
    (hC : 0 ≤ C) (hb : ∀ y, |c (s, y)| ≤ C) :
    normTwo haarAddCircle (fun x => varianceDensity c r x s) ≤
      (1 + heatConstant) * (r - s) ^ (-(1 / 2 : ℝ)) *
        normTwo haarAddCircle (fun y => c (s, y)) := by
  exact (varianceDensity_normTwo_le hc hs hC hb).trans (mul_le_mul_of_nonneg_right
    (heat_mass_small_time (sub_pos.mpr hs) hrs 0) (normTwo_nonneg _ _))

theorem spatial_normTwo_measurable {c : ℝ × HeatCircle → ℝ} (hc : Measurable c) :
    Measurable (fun s => normTwo haarAddCircle (fun y => c (s, y))) :=
  ((hc.pow_const (2 : ℕ)).stronglyMeasurable.integral_prod_right'.measurable).sqrt

set_option maxHeartbeats 1000000 in
/-- Actual positive L² transfer for the physical variance map. Spatial Young
and time Minkowski are proved above, and all section/time convergence follows
from the bounded measurable profile hypotheses. -/
theorem varianceMap_normTwo_bound {c : ℝ × HeatCircle → ℝ} {r C : ℝ}
    (hc : Measurable c) (hr : 0 < r) (hr1 : r ≤ 1) (hC : 0 ≤ C)
    (hb : ∀ s ∈ Ioo 0 r, ∀ y, |c (s, y)| ≤ C) :
    normTwo haarAddCircle (varianceMap c r) ≤
      (1 + heatConstant) * (∫ s in (0 : ℝ)..r,
        (r - s) ^ (-(1 / 2 : ℝ)) * normTwo haarAddCircle (fun y => c (s, y))) := by
  let f : ℝ → ℝ := fun s => normTwo haarAddCircle (fun y => c (s, y))
  let k : ℝ → ℝ := fun s => (r - s) ^ (-(1 / 2 : ℝ))
  let μ : Measure ℝ := volume.restrict (Ioc 0 r)
  have hf : Measurable f := spatial_normTwo_measurable hc
  have hfb : ∀ s ∈ Ioo 0 r, f s ≤ C := by
    intro s hs
    exact normTwo_bound (μ := haarAddCircle)
      (hc.comp (measurable_const.prodMk measurable_id)) hC (hb s hs)
  have hfi := (ProfileVolterra.singular_convolution_bound (a := 0) (by norm_num) hr hC hf
    (fun s _ => normTwo_nonneg _ _) (fun s hs => by simpa using hfb s hs)).1
  have hbi := (ProfileVolterra.singular_convolution_bound (a := 0) (by norm_num) hr hC
    (measurable_const : Measurable (fun _ : ℝ => C)) (fun _ _ => hC)
    (fun _ _ => by simp)).1
  have hmap : Measurable (fun p : ℝ × HeatCircle => ((r, p.2), p.1)) :=
    (measurable_const.prodMk measurable_snd).prodMk measurable_fst
  have hF' := (varianceDensity_joint_measurable hc).comp hmap
  have hF : Measurable (fun p : ℝ × HeatCircle => varianceDensity c r p.2 p.1) :=
    hF'
  have ha : Integrable (fun s => (1 + heatConstant) * (k s * f s)) μ :=
    hfi.1.const_mul _
  have hbb : Integrable (fun s => (1 + heatConstant) * (k s * C)) μ :=
    hbi.1.const_mul _
  have hgood : ∀ᵐ s ∂μ, s ∈ Ioo 0 r := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc,
      ae_restrict_of_ae (volume.ae_ne r)] with s hs hsr
    exact ⟨hs.1, lt_of_le_of_ne hs.2 hsr⟩
  have hA : 0 ≤ 1 + heatConstant := by linarith [heatConstant_pos]
  have he := bounded_minkowski_two (μ := μ) (ν := haarAddCircle) hF ha hbb
    (hgood.mono (fun s hs => mul_nonneg hA
      (mul_nonneg (Real.rpow_nonneg (by linarith [hs.2] : 0 ≤ r - s) _) (normTwo_nonneg _ _))))
    (hgood.mono (fun s hs => mul_nonneg hA
      (mul_nonneg (Real.rpow_nonneg (by linarith [hs.2] : 0 ≤ r - s) _) hC)))
    (hgood.mono (fun s hs x => by
      have hd := varianceDensity_bound hc hC hs.2 (hb s hs) x
      have hm := heat_mass_small_time (by linarith [hs.2] : 0 < r - s)
        (by linarith [hs.1] : r - s ≤ 1) x
      have he := mul_le_mul_of_nonneg_left hm hC
      apply hd.trans
      convert he using 1; ring))
    (hgood.mono (fun s hs => by
      have he := varianceDensity_normTwo_small_time hc hs.2
        (by linarith [hs.1] : r - s ≤ 1) hC (hb s hs)
      simpa only [f, k, mul_assoc] using he))
  change normTwo haarAddCircle (fun x => ∫ s in (0 : ℝ)..r, varianceDensity c r x s) ≤ _
  simpa only [varianceMap, intervalIntegral.integral_of_le hr.le, integral_const_mul, μ, f, k]
    using he

theorem normTwo_congr_ae {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {f g : X → ℝ} (he : f =ᵐ[μ] g) : normTwo μ f = normTwo μ g := by
  unfold normTwo
  congr 1
  apply integral_congr_ae
  exact he.mono (fun _ hx => congrArg (fun z : ℝ => z ^ 2) hx)

theorem normTwo_abs {X : Type*} [MeasurableSpace X] (μ : Measure X) (f : X → ℝ) :
    normTwo μ (fun x => |f x|) = normTwo μ f := by
  unfold normTwo
  simp only [sq_abs]

theorem normTwo_sum_bound {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {t f g : X → ℝ} {A B : ℝ} (ht : MemLp t 2 μ)
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hb : ∀ x, |t x| ≤ A * |f x| + B * |g x|) :
    normTwo μ t ≤ A * normTwo μ f + B * normTwo μ g := by
  have hfa : MemLp (fun x => |f x|) 2 μ := by simpa only [Real.norm_eq_abs] using hf.norm
  have hga : MemLp (fun x => |g x|) 2 μ := by simpa only [Real.norm_eq_abs] using hg.norm
  have hR := (hfa.const_mul A).add (hga.const_mul B)
  calc
    _ ≤ normTwo μ (fun x => A * |f x| + B * |g x|) := by
      apply normTwo_mono ht hR
      filter_upwards with x
      change |t x| ≤ |(A * |f x| + B * |g x|)|
      rw [abs_of_nonneg (add_nonneg (mul_nonneg hA (abs_nonneg _))
        (mul_nonneg hB (abs_nonneg _)))]
      exact hb x
    _ ≤ normTwo μ (fun x => A * |f x|) + normTwo μ (fun x => B * |g x|) :=
      normTwo_add (hfa.const_mul A) (hga.const_mul B)
    _ = _ := by
      rw [normTwo_const_mul hfa A, normTwo_const_mul hga B,
        abs_of_nonneg hA, abs_of_nonneg hB, normTwo_abs, normTwo_abs]

theorem varianceMap_normTwo_lipschitz {c d : ℝ × HeatCircle → ℝ} {r C : ℝ}
    (hc : Measurable c) (hd : Measurable d) (hr : 0 < r) (hr1 : r ≤ 1) (hC : 0 ≤ C)
    (hcB : ∀ s ∈ Ioo 0 r, ∀ y, |c (s, y)| ≤ C)
    (hdB : ∀ s ∈ Ioo 0 r, ∀ y, |d (s, y)| ≤ C) :
    normTwo haarAddCircle (fun x => varianceMap c r x - varianceMap d r x) ≤
      (1 + heatConstant) * (∫ s in (0 : ℝ)..r, (r - s) ^ (-(1 / 2 : ℝ)) *
        normTwo haarAddCircle (fun y => c (s, y) - d (s, y))) := by
  have hsub : varianceMap (c - d) r = fun x => varianceMap c r x - varianceMap d r x :=
    funext (varianceMap_sub hc hd hr hr1 hC hcB hdB)
  rw [← hsub]
  apply varianceMap_normTwo_bound (hc.sub hd) hr hr1 (by positivity : 0 ≤ 2 * C)
  intro s hs y
  exact (abs_sub _ _).trans (by linarith [hcB s hs y, hdB s hs y])

theorem varianceMap_measurable {c : ℝ × HeatCircle → ℝ} (hc : Measurable c)
    {r : ℝ} (hr : 0 ≤ r) : Measurable (varianceMap c r) := by
  have hm := (positiveVarianceMap_measurable hc).comp
    (measurable_const.prodMk measurable_id : Measurable (fun x : HeatCircle => (r, x)))
  simpa only [Function.comp_def, positiveVarianceMap_eq hr] using hm

theorem varianceMap_memLp {c : ℝ × HeatCircle → ℝ} {r C : ℝ}
    (hc : Measurable c) (hr : 0 < r) (hr1 : r ≤ 1) (hC : 0 ≤ C)
    (hb : ∀ s ∈ Ioo 0 r, ∀ y, |c (s, y)| ≤ C) :
    MemLp (varianceMap c r) 2 haarAddCircle := by
  exact bounded_memLp (varianceMap_measurable hc hr.le)
    (fun x => (varianceMap_bound hc hr hr1 hC hb x).2)

end SHE.ProfileL2
