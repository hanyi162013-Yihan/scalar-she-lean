module

public import SHE.HeatProjection

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHE.HeatProjection
open Set MeasureTheory AddCircle Real HeatTorus HeatTorusKernel CircleCorrelation
open scoped BigOperators InnerProductSpace ENNReal

/-- Fourier localization keeps a separate genuine heat operator for every
original target age. No comparability between these ages is required. -/
theorem heat_span_pairing_age_sum (q : ℕ) :
    ∃ h C θ : ℝ, 0 < h ∧ h ≤ 1 ∧ 0 < C ∧ 0 < θ ∧
      ∀ (t : Fin q → ℝ) (a : Fin q → UnitAddCircle),
      (∀ i, 0 < t i) → (∀ i, t i ≤ h) →
      ∀ e : CircleL2, e ∈ heatSpan t a → ∀ d : CircleL2,
      (∫ x : UnitAddCircle, ‖inner ℂ (translate x e) d‖ ^ 2 ∂haarAddCircle) ≤
        C * ‖e‖ ^ 2 * ∑ i, sqrt (t i) * ‖CircleHeat.heat (θ * t i) d‖ ^ 2 := by
  obtain ⟨h,C,r,hh,hh1,hC,hr,hfourier⟩ :=
    GlobalTorusHeatSpan.finite_torus_heat_span_fourier_envelope q
  let θ := r/(8*π^2)
  have hθ : 0 < θ := by dsimp [θ]; positivity
  have hθeq : 8*π^2*θ=r := by dsimp [θ]; field_simp
  refine ⟨h,C,θ,hh,hh1,hC,hθ,?_⟩
  intro t a ht hth e he d
  let f : Fin q → ℤ → ℝ := fun i n =>
    (C*‖e‖^2*sqrt (t i)) *
      (exp (-(8*π^2*(θ*t i))*(n:ℝ)^2)*‖fourierCoeff d n‖^2)
  have hf (i : Fin q) : Summable (f i) :=
    (heat_fourier_gaussian_summable (mul_pos hθ (ht i)).le d).mul_left _
  have hleft : Summable (fun n : ℤ => ‖fourierCoeff e n‖^2*‖fourierCoeff d n‖^2) := by
    simpa only [ENNReal.toReal_ofNat,Real.rpow_two,coefficient,norm_mul,norm_star,mul_pow]
      using (coefficient_memℓp e d).summable (by norm_num : (0:ℝ)<(2:ℝ≥0∞).toReal)
  rw [translated_inner_energy]
  calc
    _ ≤ ∑' n : ℤ, ∑ i : Fin q, f i n := by
      apply hleft.tsum_le_tsum _ (summable_sum (fun i _ => hf i))
      intro n
      have hb := mul_le_mul_of_nonneg_right (hfourier t a ht hth e he n) (sq_nonneg ‖fourierCoeff d n‖)
      convert! hb using 1
      simp only [f,Finset.mul_sum,Finset.sum_mul,GlobalFourierSpan.frequencyWeight]
      apply Finset.sum_congr rfl
      intro i _
      rw [show 8*π^2*(θ*t i)=r*t i by rw [← mul_assoc,hθeq]]
      ring
    _ = ∑ i : Fin q, ∑' n : ℤ, f i n := (Summable.tsum_finsetSum (fun i _ => hf i))
    _ = _ := by
      simp only [f,tsum_mul_left,← heat_norm_sq_gaussian (mul_pos hθ (ht _)).le d]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring

/-- The actual full orthogonal projection has the corresponding signed
input bound, with one heat factor for each original age. -/
theorem heat_span_projection_age_sum (q : ℕ) :
    ∃ h C θ : ℝ, 0 < h ∧ h ≤ 1 ∧ 0 < C ∧ 0 < θ ∧
      ∀ (t : Fin q → ℝ) (a : Fin q → UnitAddCircle),
      (∀ i, 0 < t i) → (∀ i, t i ≤ h) → ∀ d : CircleL2,
      Integrable (fun x : UnitAddCircle =>
        ‖(heatSpan t (fun i => a i+x)).starProjection d‖^2) haarAddCircle ∧
      (∫ x : UnitAddCircle, ‖(heatSpan t (fun i => a i+x)).starProjection d‖^2 ∂haarAddCircle) ≤
        C * ∑ i, sqrt (t i) * ‖CircleHeat.heat (θ*t i) d‖^2 := by
  classical
  obtain ⟨h,D,θ,hh,hh1,hD,hθ,hpair⟩ := heat_span_pairing_age_sum q
  refine ⟨h,D*((q:ℝ)+1),θ,hh,hh1,by positivity,hθ,?_⟩
  intro t a ht hth d
  let K := heatSpan t a
  let b := stdOrthonormalBasis ℂ K
  let e : Fin (Module.finrank ℂ K) → CircleL2 := fun i => (b i : CircleL2)
  have he : Orthonormal ℂ e := by
    convert! b.orthonormal.comp_linearIsometry K.subtypeₗᵢ using 1
  have hsp : frameSpan e=K := by
    have hbtop : Submodule.span ℂ (Set.range b)=⊤ := by
      simpa only [OrthonormalBasis.coe_toBasis] using b.toBasis.span_eq
    calc
      _ = (Submodule.span ℂ (Set.range b)).map K.subtype := by
        rw [Submodule.map_span,← Set.range_comp]
        rfl
      _ = (⊤ : Submodule ℂ K).map K.subtype := by rw [hbtop]
      _ = K := by rw [Submodule.map_top,Submodule.range_subtype]
  have hspx (x : UnitAddCircle) : frameSpan (fun i => translate x (e i))=
      heatSpan t (fun i => a i+x) := by
    calc
      _ = (frameSpan e).map (translate x).toLinearMap := by
        rw [frameSpan,frameSpan,Submodule.map_span,← Set.range_comp]
        rfl
      _ = K.map (translate x).toLinearMap := by rw [hsp]
      _ = _ := by
        dsimp only [K,heatSpan]
        rw [Submodule.map_span,← Set.range_comp]
        congr 1
        exact congrArg Set.range (funext (fun i => translate_unitHeatKernel (ht i) (a i) x))
  have hproj (x : UnitAddCircle) : (heatSpan t (fun i => a i+x)).starProjection d=
      frameProjection (fun i => translate x (e i)) d := by
    have hh : (frameSpan (fun i => translate x (e i))).starProjection d=
        frameProjection (fun i => translate x (e i)) d :=
      frameProjection_eq_starProjection _ (he.comp_linearIsometry (translate x)) d
    simpa only [hspx] using hh
  simp_rw [hproj]
  refine ⟨translated_frameProjection_integrable e he d,?_⟩
  simp_rw [translated_frameProjection_norm_sq e he d]
  rw [integral_finsetSum Finset.univ (fun i _ => translated_inner_sq_integrable (e i) d)]
  have hp (i : Fin (Module.finrank ℂ K)) :
      (∫ x : UnitAddCircle, ‖inner ℂ (translate x (e i)) d‖^2 ∂haarAddCircle) ≤
        D*∑ j, sqrt (t j)*‖CircleHeat.heat (θ*t j) d‖^2 := by
    simpa only [he.norm_eq_one i,one_pow,mul_one] using hpair t a ht hth (e i) (b i).property d
  have hcard : (Module.finrank ℂ K : ℝ) ≤ (q:ℝ)+1 := by
    have hn : Module.finrank ℂ K ≤ q := by
      simpa only [K,heatSpan,Set.finrank,Fintype.card_fin] using
        (finrank_range_le_card (R:=ℂ) (fun j : Fin q => unitHeatKernel (t j) (a j)))
    exact (show (Module.finrank ℂ K : ℝ) ≤ (q:ℝ) by exact_mod_cast hn).trans (by linarith)
  calc
    _ ≤ ∑ _i : Fin (Module.finrank ℂ K), D*∑ j, sqrt (t j)*‖CircleHeat.heat (θ*t j) d‖^2 :=
      Finset.sum_le_sum (fun i _ => hp i)
    _ = (Module.finrank ℂ K : ℝ)*(D*∑ j, sqrt (t j)*‖CircleHeat.heat (θ*t j) d‖^2) := by simp
    _ ≤ ((q:ℝ)+1)*(D*∑ j, sqrt (t j)*‖CircleHeat.heat (θ*t j) d‖^2) :=
      mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = _ := by ring

end SHE.HeatProjection
