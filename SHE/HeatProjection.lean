module

public import SHE.CircleCorrelation

/-! Genuine finite orthogonal projections onto translated physical heat
spans, and their signed one-input Haar energy. -/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace SHE.HeatProjection
open MeasureTheory Set Real SHE.HeatTorus SHE.HeatTorusKernel SHE.CircleCorrelation AddCircle
open scoped InnerProductSpace ENNReal

variable {I : Type*} [Fintype I]

def frameSpan (e : I → CircleL2) : Submodule ℂ CircleL2 := Submodule.span ℂ (Set.range e)

instance frameSpan_finiteDimensional (e : I → CircleL2) : FiniteDimensional ℂ (frameSpan e) :=
  FiniteDimensional.span_of_finite ℂ (Set.finite_range e)

def frameProjection (e : I → CircleL2) (d : CircleL2) : CircleL2 :=
  ∑ i, inner ℂ (e i) d • e i

theorem frameProjection_norm_sq (e : I → CircleL2) (he : Orthonormal ℂ e) (d : CircleL2) :
    ‖frameProjection e d‖ ^ 2 = ∑ i, ‖inner ℂ (e i) d‖ ^ 2 := by
  have h := congrArg Complex.re (he.inner_sum (fun i => inner ℂ (e i) d)
    (fun i => inner ℂ (e i) d) Finset.univ)
  simp only [Complex.conj_mul', Complex.re_sum, ← Complex.ofReal_pow, Complex.ofReal_re] at h
  calc
    _ = Complex.re (inner ℂ (frameProjection e d) (frameProjection e d)) :=
      norm_sq_eq_re_inner (𝕜 := ℂ) _
    _ = _ := h

theorem frameProjection_eq_starProjection (e : I → CircleL2) (he : Orthonormal ℂ e)
    (d : CircleL2) : (frameSpan e).starProjection d = frameProjection e d := by
  have hmem : frameProjection e d ∈ frameSpan e := by
    apply Submodule.sum_mem
    intro i _
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero hmem
  have hgen (i : I) : inner ℂ (d - frameProjection e d) (e i) = 0 := by
    rw [inner_sub_left, frameProjection, he.inner_left_fintype]
    rw [← inner_conj_symm d (e i), sub_self]
  have hker : frameSpan e ≤ LinearMap.ker (innerSL ℂ (d - frameProjection e d)).toLinearMap := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact hgen i
  intro v hv
  exact hker hv

theorem translated_frameProjection_norm_sq (e : I → CircleL2) (he : Orthonormal ℂ e)
    (d : CircleL2) (x : UnitAddCircle) :
    ‖frameProjection (fun i => translate x (e i)) d‖ ^ 2 =
      ∑ i, ‖inner ℂ (translate x (e i)) d‖ ^ 2 :=
  frameProjection_norm_sq _ (he.comp_linearIsometry (translate x)) d

theorem translated_frameProjection_integrable (e : I → CircleL2) (he : Orthonormal ℂ e)
    (d : CircleL2) :
    Integrable (fun x : UnitAddCircle => ‖frameProjection (fun i => translate x (e i)) d‖ ^ 2)
      haarAddCircle := by
  simp_rw [translated_frameProjection_norm_sq e he d]
  exact integrable_finsetSum Finset.univ (fun i _ => translated_inner_sq_integrable (e i) d)

theorem translated_frameProjection_energy (e : I → CircleL2) (he : Orthonormal ℂ e)
    (d : CircleL2) :
    (∫ x : UnitAddCircle, ‖frameProjection (fun i => translate x (e i)) d‖ ^ 2 ∂haarAddCircle) =
      ∑ i, ∑' n : ℤ, ‖fourierCoeff (e i) n‖ ^ 2 * ‖fourierCoeff d n‖ ^ 2 := by
  simp_rw [translated_frameProjection_norm_sq e he d]
  rw [integral_finsetSum Finset.univ (fun i _ => translated_inner_sq_integrable (e i) d)]
  simp_rw [translated_inner_energy]

theorem heat_norm_sq_gaussian {s : ℝ} (hs : 0 ≤ s) (d : CircleL2) :
    ‖SHE.CircleHeat.heat s d‖ ^ 2 =
      ∑' n : ℤ, exp (-(8 * π ^ 2 * s) * (n : ℝ) ^ 2) * ‖fourierCoeff d n‖ ^ 2 := by
  rw [SHE.CircleHeat.norm_sq_fourier]
  apply tsum_congr
  intro n
  rw [SHE.CircleHeat.heat_fourierCoeff, norm_mul, mul_pow, SHE.CircleHeat.heatWeight_norm_sq hs]
  congr 2
  ring

theorem heat_fourier_gaussian_summable {s : ℝ} (hs : 0 ≤ s) (d : CircleL2) :
    Summable (fun n : ℤ => exp (-(8 * π ^ 2 * s) * (n : ℝ) ^ 2) * ‖fourierCoeff d n‖ ^ 2) := by
  convert! SHE.CircleHeat.summable_fourier_sq (SHE.CircleHeat.heat s d) using 1
  funext n
  rw [SHE.CircleHeat.heat_fourierCoeff, norm_mul, mul_pow, SHE.CircleHeat.heatWeight_norm_sq hs]
  congr 2
  ring

/-- A genuine Fourier envelope turns the actual translated pairing into one
signed smoothed L² input. It does not require an absolute value heat operator. -/
theorem translated_inner_heat_bound (e d : CircleL2) {A s : ℝ} (_hA : 0 ≤ A) (hs : 0 ≤ s)
    (hcoef : ∀ n : ℤ, ‖fourierCoeff e n‖ ^ 2 ≤ A * exp (-(8 * π ^ 2 * s) * (n : ℝ) ^ 2)) :
    (∫ x : UnitAddCircle, ‖inner ℂ (translate x e) d‖ ^ 2 ∂haarAddCircle) ≤
      A * ‖SHE.CircleHeat.heat s d‖ ^ 2 := by
  rw [translated_inner_energy]
  have hsleft : Summable (fun n : ℤ => ‖fourierCoeff e n‖ ^ 2 * ‖fourierCoeff d n‖ ^ 2) := by
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two, coefficient, norm_mul, norm_star, mul_pow]
      using (coefficient_memℓp e d).summable (by norm_num : (0 : ℝ) < (2 : ℝ≥0∞).toReal)
  calc
    _ ≤ ∑' n : ℤ, A * (exp (-(8 * π ^ 2 * s) * (n : ℝ) ^ 2) * ‖fourierCoeff d n‖ ^ 2) := by
      apply hsleft.tsum_le_tsum _ ((heat_fourier_gaussian_summable hs d).mul_left A)
      intro n
      have h := mul_le_mul_of_nonneg_right (hcoef n) (sq_nonneg ‖fourierCoeff d n‖)
      simpa only [mul_assoc] using h
    _ = _ := by rw [tsum_mul_left, ← heat_norm_sq_gaussian hs d]

theorem frequencyWeight_le_common {r t w M : ℝ} (hr : 0 ≤ r) (hw : 0 < w)
    (hM : 1 ≤ M) (hlo : w ≤ t) (hhi : t ≤ M * w) (n : ℤ) :
    SHE.GlobalFourierSpan.frequencyWeight r t (n : ℝ) ≤
      sqrt M * sqrt w * exp (-r * w * (n : ℝ) ^ 2) := by
  have hroot : sqrt t ≤ sqrt M * sqrt w := by
    rw [← sqrt_mul (zero_le_one.trans hM)]
    exact sqrt_le_sqrt hhi
  have hphase : exp (-r * t * (n : ℝ) ^ 2) ≤ exp (-r * w * (n : ℝ) ^ 2) := by
    apply exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_right hlo (mul_nonneg hr (sq_nonneg (n : ℝ)))]
  exact mul_le_mul hroot hphase (exp_pos _).le (by positivity)

/-- The actual one-input estimate for every vector in a finite physical heat
span. The heat factor acts on the signed input before its L² norm is taken. -/
theorem finite_heat_span_pairing_bound (q : ℕ) :
    ∃ h C θ : ℝ, 0 < h ∧ h ≤ 1 ∧ 0 < C ∧ 0 < θ ∧
      ∀ (t : Fin q → ℝ) (a : Fin q → UnitAddCircle), (∀ i, 0 < t i) → (∀ i, t i ≤ h) →
      ∀ (w M : ℝ), 0 < w → 1 ≤ M → (∀ i, w ≤ t i) → (∀ i, t i ≤ M * w) →
      ∀ e : CircleL2, e ∈ Submodule.span ℂ (Set.range (fun i => unitHeatKernel (t i) (a i))) →
      ∀ d : CircleL2,
      (∫ x : UnitAddCircle, ‖inner ℂ (translate x e) d‖ ^ 2 ∂haarAddCircle) ≤
        C * sqrt M * sqrt w * ‖e‖ ^ 2 * ‖SHE.CircleHeat.heat (θ * w) d‖ ^ 2 := by
  obtain ⟨h, D, r, hh, hh1, hD, hr, hfourier⟩ :=
    SHE.GlobalTorusHeatSpan.finite_torus_heat_span_fourier_envelope q
  let C : ℝ := D * ((q : ℝ) + 1)
  let θ : ℝ := r / (8 * π ^ 2)
  have hC : 0 < C := by dsimp only [C]; positivity
  have hθ : 0 < θ := by dsimp only [θ]; positivity
  have hθeq : 8 * π ^ 2 * θ = r := by
    dsimp only [θ]
    field_simp
  refine ⟨h, C, θ, hh, hh1, hC, hθ, ?_⟩
  intro t a ht hth w M hw hM hlo hhi e he d
  have hcoef (n : ℤ) : ‖fourierCoeff e n‖ ^ 2 ≤
      (C * sqrt M * sqrt w * ‖e‖ ^ 2) * exp (-(8 * π ^ 2 * (θ * w)) * (n : ℝ) ^ 2) := by
    have hh := hfourier t a ht hth e he n
    have hsum : (∑ i, SHE.GlobalFourierSpan.frequencyWeight r (t i) (n : ℝ)) ≤
        (q : ℝ) * (sqrt M * sqrt w * exp (-r * w * (n : ℝ) ^ 2)) := by
      calc
        _ ≤ ∑ _ : Fin q, sqrt M * sqrt w * exp (-r * w * (n : ℝ) ^ 2) :=
          Finset.sum_le_sum (fun i _ => frequencyWeight_le_common hr.le hw hM (hlo i) (hhi i) n)
        _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hCq : D * (q : ℝ) ≤ C := by dsimp only [C]; nlinarith
    have hm := mul_le_mul_of_nonneg_right hCq
      (show 0 ≤ sqrt M * sqrt w * ‖e‖ ^ 2 * exp (-r * w * (n : ℝ) ^ 2) by positivity)
    have hfirst := hh.trans (mul_le_mul_of_nonneg_left hsum (by positivity : 0 ≤ D * ‖e‖ ^ 2))
    have heq : 8 * π ^ 2 * (θ * w) = r * w := by rw [← mul_assoc, hθeq]
    rw [heq]
    calc
      _ ≤ D * ‖e‖ ^ 2 * ((q : ℝ) * (sqrt M * sqrt w * exp (-r * w * (n : ℝ) ^ 2))) := hfirst
      _ = (D * (q : ℝ)) * (sqrt M * sqrt w * ‖e‖ ^ 2 * exp (-r * w * (n : ℝ) ^ 2)) := by ring
      _ ≤ C * (sqrt M * sqrt w * ‖e‖ ^ 2 * exp (-r * w * (n : ℝ) ^ 2)) := hm
      _ = _ := by
        have hp : -r * w * (n : ℝ) ^ 2 = -(r * w) * (n : ℝ) ^ 2 := by ring
        rw [hp]
        ring
  exact translated_inner_heat_bound e d (by positivity) (mul_pos hθ hw).le hcoef

theorem heat_span_frame_card_le (q : ℕ) (t : Fin q → ℝ) (a : Fin q → UnitAddCircle)
    (e : I → CircleL2) (he : Orthonormal ℂ e)
    (hspan : ∀ i, e i ∈ Submodule.span ℂ (Set.range (fun j => unitHeatKernel (t j) (a j)))) :
    Fintype.card I ≤ q := by
  classical
  let K : Submodule ℂ CircleL2 := Submodule.span ℂ (Set.range (fun j => unitHeatKernel (t j) (a j)))
  have : FiniteDimensional ℂ K := FiniteDimensional.span_of_finite ℂ (Set.finite_range _)
  let eK : I → K := fun i => ⟨e i, hspan i⟩
  have heK : Orthonormal ℂ eK := by
    rw [orthonormal_iff_ite] at he ⊢
    exact he
  have hcard := heK.linearIndependent.fintype_card_le_finrank
  have hdim : Module.finrank ℂ K ≤ q := by
    simpa only [K, Set.finrank, Fintype.card_fin] using
      (finrank_range_le_card (R := ℂ) (fun j : Fin q => unitHeatKernel (t j) (a j)))
  exact hcard.trans hdim

/-- Collision-uniform translated finite-span projection estimate. The map
inside the norm is the actual orthogonal projection, and the signed input
keeps a genuine positive heat factor. The constant depends only on q. -/
theorem finite_heat_span_projection_bound (q : ℕ) :
    ∃ h C θ : ℝ, 0 < h ∧ h ≤ 1 ∧ 0 < C ∧ 0 < θ ∧
      ∀ (t : Fin q → ℝ) (a : Fin q → UnitAddCircle), (∀ i, 0 < t i) → (∀ i, t i ≤ h) →
      ∀ (w M : ℝ), 0 < w → 1 ≤ M → (∀ i, w ≤ t i) → (∀ i, t i ≤ M * w) →
      ∀ (r : ℕ) (e : Fin r → CircleL2), Orthonormal ℂ e →
      (∀ i, e i ∈ Submodule.span ℂ (Set.range (fun j => unitHeatKernel (t j) (a j)))) →
      ∀ d : CircleL2,
      Integrable (fun x : UnitAddCircle => ‖(frameSpan (fun i => translate x (e i))).starProjection d‖ ^ 2)
        haarAddCircle ∧
      (∫ x : UnitAddCircle, ‖(frameSpan (fun i => translate x (e i))).starProjection d‖ ^ 2 ∂haarAddCircle) ≤
        C * sqrt M * sqrt w * ‖SHE.CircleHeat.heat (θ * w) d‖ ^ 2 := by
  obtain ⟨h, D, θ, hh, hh1, hD, hθ, hpair⟩ := finite_heat_span_pairing_bound q
  let C : ℝ := D * ((q : ℝ) + 1)
  have hC : 0 < C := by dsimp only [C]; positivity
  refine ⟨h, C, θ, hh, hh1, hC, hθ, ?_⟩
  intro t a ht hth w M hw hM hlo hhi r e he hspan d
  have hprojection (x : UnitAddCircle) :
      (frameSpan (fun i => translate x (e i))).starProjection d =
        frameProjection (fun i => translate x (e i)) d :=
    frameProjection_eq_starProjection _ (he.comp_linearIsometry (translate x)) d
  simp_rw [hprojection]
  refine ⟨translated_frameProjection_integrable e he d, ?_⟩
  have hpoint (i : Fin r) :
      (∫ x : UnitAddCircle, ‖inner ℂ (translate x (e i)) d‖ ^ 2 ∂haarAddCircle) ≤
        D * sqrt M * sqrt w * ‖SHE.CircleHeat.heat (θ * w) d‖ ^ 2 := by
    have h := hpair t a ht hth w M hw hM hlo hhi (e i) (hspan i) d
    simpa only [he.norm_eq_one i, one_pow, mul_one] using h
  have hframe :
      (∫ x : UnitAddCircle, ‖frameProjection (fun i => translate x (e i)) d‖ ^ 2 ∂haarAddCircle) ≤
        (r : ℝ) * (D * sqrt M * sqrt w * ‖SHE.CircleHeat.heat (θ * w) d‖ ^ 2) := by
    simp_rw [translated_frameProjection_norm_sq e he d]
    rw [integral_finsetSum Finset.univ (fun i _ => translated_inner_sq_integrable (e i) d)]
    calc
      _ ≤ ∑ _ : Fin r, D * sqrt M * sqrt w * ‖SHE.CircleHeat.heat (θ * w) d‖ ^ 2 :=
        Finset.sum_le_sum (fun i _ => hpoint i)
      _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hcard : (r : ℝ) ≤ (q : ℝ) + 1 := by
    have hnat := heat_span_frame_card_le q t a e he hspan
    simp only [Fintype.card_fin] at hnat
    exact (by exact_mod_cast hnat : (r : ℝ) ≤ (q : ℝ)).trans (by linarith)
  have hm := mul_le_mul_of_nonneg_right hcard
    (show 0 ≤ D * sqrt M * sqrt w * ‖SHE.CircleHeat.heat (θ * w) d‖ ^ 2 by positivity)
  apply hframe.trans
  convert! hm using 1
  dsimp only [C]
  ring

def heatSpan {q : ℕ} (t : Fin q → ℝ) (a : Fin q → UnitAddCircle) : Submodule ℂ CircleL2 :=
  Submodule.span ℂ (Set.range (fun i => unitHeatKernel (t i) (a i)))

instance heatSpan_finiteDimensional {q : ℕ} (t : Fin q → ℝ) (a : Fin q → UnitAddCircle) :
    FiniteDimensional ℂ (heatSpan t a) :=
  FiniteDimensional.span_of_finite ℂ (Set.finite_range _)

/-- The canonical full heat span, with no chosen basis or frame left in the
statement. This is the literal translated finite-span one-input estimate. -/
theorem translated_heat_span_projection_bound (q : ℕ) :
    ∃ h C θ : ℝ, 0 < h ∧ h ≤ 1 ∧ 0 < C ∧ 0 < θ ∧
      ∀ (t : Fin q → ℝ) (a : Fin q → UnitAddCircle), (∀ i, 0 < t i) → (∀ i, t i ≤ h) →
      ∀ (w M : ℝ), 0 < w → 1 ≤ M → (∀ i, w ≤ t i) → (∀ i, t i ≤ M * w) →
      ∀ d : CircleL2,
      Integrable (fun x : UnitAddCircle => ‖(heatSpan t (fun i => a i + x)).starProjection d‖ ^ 2)
        haarAddCircle ∧
      (∫ x : UnitAddCircle, ‖(heatSpan t (fun i => a i + x)).starProjection d‖ ^ 2 ∂haarAddCircle) ≤
        C * sqrt M * sqrt w * ‖SHE.CircleHeat.heat (θ * w) d‖ ^ 2 := by
  classical
  obtain ⟨h, C, θ, hh, hh1, hC, hθ, hproj⟩ := finite_heat_span_projection_bound q
  refine ⟨h, C, θ, hh, hh1, hC, hθ, ?_⟩
  intro t a ht hth w M hw hM hlo hhi d
  let K := heatSpan t a
  let b := stdOrthonormalBasis ℂ K
  let e : Fin (Module.finrank ℂ K) → CircleL2 := fun i => (b i : CircleL2)
  have he : Orthonormal ℂ e := by
    convert! b.orthonormal.comp_linearIsometry K.subtypeₗᵢ using 1
  have hsp : frameSpan e = K := by
    have hbtop : Submodule.span ℂ (Set.range b) = ⊤ := by
      simpa only [OrthonormalBasis.coe_toBasis] using b.toBasis.span_eq
    calc
      _ = (Submodule.span ℂ (Set.range b)).map K.subtype := by
        rw [Submodule.map_span, ← Set.range_comp]
        rfl
      _ = (⊤ : Submodule ℂ K).map K.subtype := by rw [hbtop]
      _ = K := by rw [Submodule.map_top, Submodule.range_subtype]
  have hspx (x : UnitAddCircle) : frameSpan (fun i => translate x (e i)) =
      heatSpan t (fun i => a i + x) := by
    calc
      _ = (frameSpan e).map (translate x).toLinearMap := by
        rw [frameSpan, frameSpan, Submodule.map_span, ← Set.range_comp]
        rfl
      _ = K.map (translate x).toLinearMap := by rw [hsp]
      _ = _ := by
        dsimp only [K, heatSpan]
        rw [Submodule.map_span, ← Set.range_comp]
        apply congrArg (Submodule.span ℂ)
        apply congrArg Set.range
        funext i
        exact translate_unitHeatKernel (ht i) (a i) x
  have hb := hproj t a ht hth w M hw hM hlo hhi (Module.finrank ℂ K) e he
    (fun i => (b i).property) d
  simpa only [hspx] using hb

end SHE.HeatProjection
