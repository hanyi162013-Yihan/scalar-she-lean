module

public import SHE.HeatSpanCluster
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-! Physical affine rescaling of the collision-uniform compact Gaussian span
bound. All energies are actual Lebesgue integrals on the line. -/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace SHE.HeatLine
open MeasureTheory Set SHE.HeatAnnihilator SHE.HeatSpanCluster

def affineParameter (p : Parameter) (c s : ℂ) : Parameter :=
  (p.1 * s ^ 2, s * (p.2 - 2 * p.1 * c))

theorem gaussian_affine (p : Parameter) (c s z : ℂ) :
    gaussian p (c + s * z) = gaussian p c * gaussian (affineParameter p c s) z := by
  unfold gaussian affineParameter
  rw [← Complex.exp_add]
  congr 1
  ring

theorem affine_gaussian_span {q : ℕ} (base : Fin q → Parameter) (f : ℂ → ℂ)
    (hf : f ∈ Submodule.span ℂ (Set.range (fun i => gaussian (base i)))) (c s : ℂ) :
    (fun z : ℂ => f (c + s * z)) ∈ Submodule.span ℂ
      (Set.range (fun i => gaussian (affineParameter (base i) c s))) := by
  obtain ⟨d, hd⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hf
  apply (Submodule.mem_span_range_iff_exists_fun ℂ).mpr
  refine ⟨fun i => d i * gaussian (base i) c, ?_⟩
  funext z
  have hdz := congrFun hd (c + s * z)
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at hdz ⊢
  rw [← hdz]
  apply Finset.sum_congr rfl
  intro i _
  rw [gaussian_affine]
  ring

theorem integral_affine {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ → E) (c s : ℝ) :
    (∫ x : ℝ, f (c + s * x)) = |s⁻¹| • ∫ y : ℝ, f y := by
  rw [Measure.integral_comp_mul_left (fun y => f (c + y)) s,
    integral_add_left_eq_self f c]

theorem integrable_affine_iff {E : Type*} [NormedAddCommGroup E]
    (f : ℝ → E) (c : ℝ) {s : ℝ} (hs : s ≠ 0) :
    Integrable (fun x : ℝ => f (c + s * x)) ↔ Integrable f := by
  have h := integrable_comp_smul_iff volume (fun y : ℝ => f (c + y)) hs
  exact h.trans ((measurePreserving_add_left volume c).integrable_comp_emb
    (MeasurableEquiv.addLeft c).measurableEmbedding)

/-- Affine-scaled compact localization. The hypotheses constrain the actual
normalized Gaussian parameters, while the conclusion uses the original
physical center, scale, and global line energy. -/
theorem affine_gaussian_span_global_envelope (q : ℕ) (R : ℝ) {γ k B : ℝ}
    (hγ : 0 < γ) (hk : 0 < k) :
    ∃ C : ℝ, 0 < C ∧ ∀ (base : Fin q → Parameter) (c s : ℝ), 0 < s →
      ‖fun i => affineParameter (base i) (c : ℂ) (s : ℂ)‖ ≤ R →
      (∀ i, γ + k ≤ (affineParameter (base i) c s).1.re) →
      (∀ i, |(affineParameter (base i) c s).2.re| ≤ B) →
      ∀ (f : ℂ → ℂ), f ∈ Submodule.span ℂ (Set.range (fun i => gaussian (base i))) →
      Integrable (fun u : ℝ => ‖f (u : ℂ)‖ ^ 2) ∧
      ∀ x : ℝ, ‖f (x : ℂ)‖ ^ 2 ≤ C * s⁻¹ * (∫ u : ℝ, ‖f (u : ℂ)‖ ^ 2) *
        Real.exp (-(2 * γ) * ((x - c) / s) ^ 2) := by
  obtain ⟨C, hC, hbound⟩ := bounded_gaussian_span_global_envelope q R hγ hk
  refine ⟨C, hC, ?_⟩
  intro base c s hs hp ha hb f hf
  let g : ℂ → ℂ := fun z => f ((c : ℂ) + (s : ℂ) * z)
  obtain ⟨hig, hbg⟩ := hbound _ hp ha hb g (affine_gaussian_span base f hf c s)
  have hcast (u : ℝ) : g (u : ℂ) = f ((c + s * u : ℝ) : ℂ) := by
    simp only [g, Complex.ofReal_add, Complex.ofReal_mul]
  have hi : Integrable (fun u : ℝ => ‖f (u : ℂ)‖ ^ 2) := by
    apply (integrable_affine_iff (fun u : ℝ => ‖f (u : ℂ)‖ ^ 2) c hs.ne').mp
    simpa only [hcast] using hig
  refine ⟨hi, ?_⟩
  intro x
  have hx : c + s * ((x - c) / s) = x := by field_simp; ring
  have h := hbg ((x - c) / s)
  simp only [hcast, hx] at h
  have he : (∫ u : ℝ, ‖f ((c + s * u : ℝ) : ℂ)‖ ^ 2) =
      s⁻¹ * ∫ u : ℝ, ‖f (u : ℂ)‖ ^ 2 := by
    convert! integral_affine (fun u : ℝ => ‖f (u : ℂ)‖ ^ 2) c s using 1
    rw [abs_of_pos (inv_pos.mpr hs), smul_eq_mul]
  rw [he] at h
  convert! h using 1
  ring

def heatParameter (t a : ℝ) : Parameter :=
  ((1 / (4 * t) : ℝ), (a / (2 * t) : ℝ))

def heatEntire (t a : ℝ) (z : ℂ) : ℂ :=
  Complex.exp (-((z - (a : ℂ)) ^ 2) / (4 * (t : ℂ)))

theorem heatEntire_eq_gaussian (t a : ℝ) :
    heatEntire t a = fun z => Complex.exp (-((a : ℂ) ^ 2) / (4 * (t : ℂ))) *
      gaussian (heatParameter t a) z := by
  funext z
  unfold heatEntire gaussian heatParameter
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem heat_span_gaussian {q : ℕ} (t a : Fin q → ℝ) (f : ℂ → ℂ)
    (hf : f ∈ Submodule.span ℂ (Set.range (fun i => heatEntire (t i) (a i)))) :
    f ∈ Submodule.span ℂ (Set.range (fun i => gaussian (heatParameter (t i) (a i)))) := by
  have hle : Submodule.span ℂ (Set.range (fun i => heatEntire (t i) (a i))) ≤
      Submodule.span ℂ (Set.range (fun i => gaussian (heatParameter (t i) (a i)))) :=
    Submodule.span_le.mpr (by
      rintro _ ⟨i, rfl⟩
      change heatEntire (t i) (a i) ∈ _
      rw [heatEntire_eq_gaussian]
      change Complex.exp (-((a i : ℂ) ^ 2) / (4 * (t i : ℂ))) • gaussian (heatParameter (t i) (a i)) ∈ _
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩))
  exact hle hf

theorem heat_affineParameter (t a c s : ℝ) :
    affineParameter (heatParameter t a) c s =
      (((s ^ 2 / (4 * t) : ℝ) : ℂ), ((s * (a - c) / (2 * t) : ℝ) : ℂ)) := by
  unfold affineParameter heatParameter
  ext <;> push_cast <;> ring

theorem heat_normalized_parameters {t a c T δ B : ℝ} (hT : 0 < T) (hδ : 0 < δ)
    (hB : 0 ≤ B) (ht : δ * T ≤ t) (htT : t ≤ T) (ha : |a - c| ≤ B * Real.sqrt T) :
    ‖affineParameter (heatParameter t a) c (Real.sqrt T)‖ ≤
        max (1 / (4 * δ)) (B / (2 * δ)) ∧
      (1 / 4 : ℝ) ≤ (affineParameter (heatParameter t a) c (Real.sqrt T)).1.re ∧
      |(affineParameter (heatParameter t a) c (Real.sqrt T)).2.re| ≤ B / (2 * δ) := by
  have htpos : 0 < t := (mul_pos hδ hT).trans_le ht
  rw [heat_affineParameter, Real.sq_sqrt hT.le]
  have ha0 : 0 ≤ T / (4 * t) := by positivity
  have ha1 : T / (4 * t) ≤ 1 / (4 * δ) := by
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    nlinarith
  have ha2 : (1 / 4 : ℝ) ≤ T / (4 * t) := by
    apply (le_div_iff₀ (by positivity)).mpr
    nlinarith
  have hb : |Real.sqrt T * (a - c) / (2 * t)| ≤ B / (2 * δ) := by
    rw [abs_div, abs_of_pos (by positivity : 0 < 2 * t), abs_mul,
      abs_of_nonneg (Real.sqrt_nonneg _)]
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    have h := mul_le_mul_of_nonneg_left ha (Real.sqrt_nonneg T)
    have hs : Real.sqrt T * (B * Real.sqrt T) = B * T := by
      nlinarith [Real.sq_sqrt hT.le]
    rw [hs] at h
    nlinarith [mul_le_mul_of_nonneg_left ht hB]
  refine ⟨?_, ha2, ?_⟩
  · rw [Prod.norm_def, Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg ha0]
    exact max_le_max ha1 hb
  · simpa only [Complex.ofReal_re] using hb

/-- Collision-uniform physical localization of a compact heat cluster.
Only the internal age ratio and normalized center radius enter the constant.
There is no separation requirement and no condition on coefficients. -/
theorem compact_heat_cluster_envelope (q : ℕ) {δ B : ℝ} (hδ : 0 < δ) (hB : 0 ≤ B) :
    ∃ C : ℝ, 0 < C ∧ ∀ (t a : Fin q → ℝ) (T c : ℝ), 0 < T →
      (∀ i, δ * T ≤ t i) → (∀ i, t i ≤ T) →
      (∀ i, |a i - c| ≤ B * Real.sqrt T) →
      ∀ (f : ℂ → ℂ), f ∈ Submodule.span ℂ (Set.range (fun i => heatEntire (t i) (a i))) →
      Integrable (fun u : ℝ => ‖f (u : ℂ)‖ ^ 2) ∧
      ∀ x : ℝ, ‖f (x : ℂ)‖ ^ 2 ≤ C * (Real.sqrt T)⁻¹ *
        (∫ u : ℝ, ‖f (u : ℂ)‖ ^ 2) * Real.exp (-(x - c) ^ 2 / (4 * T)) := by
  obtain ⟨C, hC, hbound⟩ := affine_gaussian_span_global_envelope q
    (max (1 / (4 * δ)) (B / (2 * δ)))
    (γ := 1 / 8) (k := 1 / 8) (B := B / (2 * δ)) (by norm_num) (by norm_num)
  refine ⟨C, hC, ?_⟩
  intro t a T c hT ht htT ha f hf
  have hp := fun i => heat_normalized_parameters hT hδ hB (ht i) (htT i) (ha i)
  have hR : 0 ≤ max (1 / (4 * δ)) (B / (2 * δ)) := le_max_of_le_left (by positivity)
  obtain ⟨hi, hb⟩ := hbound (fun i => heatParameter (t i) (a i)) c (Real.sqrt T)
    (Real.sqrt_pos.mpr hT) ((pi_norm_le_iff_of_nonneg hR).mpr (fun i => (hp i).1))
    (by intro i; convert (hp i).2.1 using 1; norm_num)
    (fun i => (hp i).2.2) f (heat_span_gaussian t a f hf)
  refine ⟨hi, ?_⟩
  intro x
  have he : -(2 * (1 / 8 : ℝ)) * ((x - c) / Real.sqrt T) ^ 2 =
      -(x - c) ^ 2 / (4 * T) := by
    rw [div_pow, Real.sq_sqrt hT.le]
    ring
  simpa only [he] using hb x

end SHE.HeatLine
