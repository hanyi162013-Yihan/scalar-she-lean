module

public import SHE.HeatTorus

/-! Exact identification of normalized Gaussian periodization with the
physical spectral circle heat kernel, and genuine Haar translations. -/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace SHE.HeatTorusKernel
open MeasureTheory Set Real SHE.HeatLine SHE.HeatPeriodization SHE.HeatTorus
  SHE.FourierHeatLine SHE.FourierCluster SHE.FourierParseval AddCircle
open scoped FourierTransform

local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

def unitHeatKernel (t : ℝ) (a : UnitAddCircle) : CircleL2 :=
  SHE.CircleNormalization.pull 1 (2 * Real.pi)
    (SHE.StoppedFourier.circleHeat (4 * Real.pi ^ 2 * t)
      (SHE.CircleNormalization.scale 1 (2 * Real.pi) a))

theorem fourierCoeff_unitHeatKernel {t : ℝ} (ht : 0 < t) (a : UnitAddCircle) (n : ℤ) :
    fourierCoeff (unitHeatKernel t a) n =
      fourier (-n) a * (Real.exp (-(4 * Real.pi ^ 2 * t) * (n : ℝ) ^ 2) : ℂ) := by
  unfold unitHeatKernel
  rw [SHE.CircleNormalization.fourierCoeff_pull,
    SHE.StoppedFourier.circleHeat_fourierCoeff (by positivity), SHE.StoppedFourier.heatCoeff,
    SHE.CircleNormalization.fourier_scale]

theorem frequencyGaussian_integer (t a : ℝ) (n : ℤ) :
    frequencyGaussian t a (n : ℂ) = fourier (-n) (a : UnitAddCircle) *
      (Real.exp (-(4 * Real.pi ^ 2 * t) * (n : ℝ) ^ 2) : ℂ) := by
  unfold frequencyGaussian SHE.HeatAnnihilator.gaussian frequencyParameter
  rw [fourier_coe_apply, Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  push_cast
  ring

def translate (c : UnitAddCircle) : CircleL2 →ₗᵢ[ℂ] CircleL2 :=
  Lp.compMeasurePreservingₗᵢ ℂ (fun x => x - c)
    (measurePreserving_sub_right AddCircle.haarAddCircle c)

theorem translate_ae (c : UnitAddCircle) (f : CircleL2) :
    translate c f =ᵐ[AddCircle.haarAddCircle] fun x => f (x - c) :=
  Lp.coeFn_compMeasurePreserving f (measurePreserving_sub_right AddCircle.haarAddCircle c)

theorem translate_norm (c : UnitAddCircle) (f : CircleL2) : ‖translate c f‖ = ‖f‖ :=
  (translate c).norm_map f

theorem fourier_argument_add (n : ℤ) (x y : UnitAddCircle) :
    fourier n (x + y) = fourier n x * fourier n y := by
  simp only [fourier_apply, zsmul_add, AddCircle.toCircle_add, Circle.coe_mul]

theorem fourierCoeff_translate (c : UnitAddCircle) (f : CircleL2) (n : ℤ) :
    fourierCoeff (translate c f) n = fourier (-n) c * fourierCoeff f n := by
  unfold fourierCoeff
  calc
    _ = ∫ x : UnitAddCircle, fourier (-n) x * f (x - c) ∂haarAddCircle := by
      apply integral_congr_ae
      filter_upwards [translate_ae c f] with x hx
      rw [hx, smul_eq_mul]
    _ = ∫ x : UnitAddCircle, fourier (-n) (x + c) * f x ∂haarAddCircle := by
      have h := integral_add_right_eq_self (μ := haarAddCircle)
        (fun x : UnitAddCircle => fourier (-n) x * f (x - c)) c
      simpa only [add_sub_cancel_right] using h.symm
    _ = _ := by
      simp_rw [fourier_argument_add, mul_right_comm _ (fourier (-n) c), mul_comm _ (fourier (-n) c)]
      rw [integral_const_mul]
      rfl

theorem translate_unitHeatKernel {t : ℝ} (ht : 0 < t) (a c : UnitAddCircle) :
    translate c (unitHeatKernel t a) = unitHeatKernel t (a + c) := by
  apply (fourierBasis (T := 1)).repr.injective
  apply lp.ext
  funext n
  simp only [fourierBasis_repr, fourierCoeff_translate, fourierCoeff_unitHeatKernel ht,
    fourier_argument_add]
  ring

theorem periodizationL2_eq_heat_sum {q : ℕ} (t a : Fin q → ℝ) (ht : ∀ i, 0 < t i)
    (f : ℂ → ℂ) (hf : f ∈ Submodule.span ℂ (Set.range (fun i => heatEntire (t i) (a i))))
    (z : Fin q → ℂ) (hz : (∑ i, z i • heatEntire (t i) (a i)) = f) :
    periodizationL2 t a ht f hf =
      ∑ i, (z i * (heatMass (t i) : ℂ)) • unitHeatKernel (t i) (a i : UnitAddCircle) := by
  apply (fourierBasis (T := 1)).repr.injective
  apply lp.ext
  funext n
  rw [map_sum]
  simp only [lp.coeFn_sum, Finset.sum_apply, map_smul, lp.coeFn_smul, Pi.smul_apply,
    smul_eq_mul, fourierBasis_repr, periodizationL2_fourierCoeff]
  have hfun : (fun x : ℝ => f (x : ℂ)) = physicalSum t a z := by
    funext x
    have h := congrFun hz (x : ℂ)
    simpa only [physicalSum, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using h.symm
  rw [hfun, fourier_physicalSum t a z ht]
  unfold frequencySum
  apply Finset.sum_congr rfl
  intro i _
  simp only [Complex.ofReal_intCast]
  rw [fourierCoeff_unitHeatKernel (ht i), frequencyGaussian_integer]

/-- Every physical finite circle heat combination is literally a normalized
periodization of one line heat combination with the chosen real lifts. -/
theorem exists_line_lift_of_heat_sum {q : ℕ} (t a : Fin q → ℝ) (ht : ∀ i, 0 < t i)
    (z : Fin q → ℂ) :
    ∃ (f : ℂ → ℂ) (hf : f ∈ Submodule.span ℂ (Set.range (fun i => heatEntire (t i) (a i)))),
      periodizationL2 t a ht f hf = ∑ i, z i • unitHeatKernel (t i) (a i : UnitAddCircle) := by
  let d : Fin q → ℂ := fun i => z i / (heatMass (t i) : ℂ)
  let f : ℂ → ℂ := ∑ i, d i • heatEntire (t i) (a i)
  have hf : f ∈ Submodule.span ℂ (Set.range (fun i => heatEntire (t i) (a i))) :=
    physicalSum_span t a d
  refine ⟨f, hf, ?_⟩
  rw [periodizationL2_eq_heat_sum t a ht f hf d rfl]
  apply Finset.sum_congr rfl
  intro i _
  have hm : (heatMass (t i) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (heatMass_pos (ht i)).ne'
  simp only [d, div_mul_cancel₀ _ hm]

def continuousTranslate (c : UnitAddCircle) (f : C(UnitAddCircle, ℂ)) : C(UnitAddCircle, ℂ) :=
  ⟨fun x => f (x - c), by fun_prop⟩

theorem toLp_continuousTranslate (c : UnitAddCircle) (f : C(UnitAddCircle, ℂ)) :
    ContinuousMap.toLp 2 haarAddCircle ℂ (continuousTranslate c f) =
      translate c (ContinuousMap.toLp 2 haarAddCircle ℂ f) := by
  apply Lp.ext
  have hpres := (measurePreserving_sub_right haarAddCircle c).quasiMeasurePreserving
  filter_upwards [ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) haarAddCircle (continuousTranslate c f),
    translate_ae c (ContinuousMap.toLp 2 haarAddCircle ℂ f),
    hpres.ae (ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) haarAddCircle f)] with x hx hy hz
  rw [hx, hy, hz]
  rfl

theorem circle_margin_le_one (q : ℕ) : SHE.CircleCut.margin q ≤ 1 := by
  unfold SHE.CircleCut.margin
  apply (div_le_one (show 0 < 4 * ((q : ℝ) + 1) by positivity)).mpr
  nlinarith [show 0 ≤ (q : ℝ) by positivity]

/-- A common geometric cut and a genuine line lift for every finite physical
circle heat span, with exact Haar translation back to the original field. -/
theorem exists_cut_line_lift (q : ℕ) (t : Fin q → ℝ) (a : Fin q → UnitAddCircle)
    (ht : ∀ i, 0 < t i) (F : CircleL2)
    (hF : F ∈ Submodule.span ℂ (Set.range (fun i => unitHeatKernel (t i) (a i)))) :
    ∃ (c : UnitAddCircle) (b : Fin q → ℝ) (f : ℂ → ℂ)
      (hf : f ∈ Submodule.span ℂ (Set.range (fun i => heatEntire (t i) (b i)))),
      (∀ i, (b i : UnitAddCircle) + c = a i) ∧
      (∀ i, |b i| ≤ 1 / 2 - SHE.CircleCut.margin q) ∧
      translate c (periodizationL2 t b ht f hf) = F := by
  obtain ⟨c, b, hb, hmargin⟩ := SHE.CircleCut.exists_interior_lifts q a
  obtain ⟨z, hz⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hF
  obtain ⟨f, hf, hlift⟩ := exists_line_lift_of_heat_sum t b ht z
  refine ⟨c, b, f, hf, hb, hmargin, ?_⟩
  rw [hlift, map_sum]
  simp only [map_smul]
  rw [← hz]
  apply Finset.sum_congr rfl
  intro i _
  rw [translate_unitHeatKernel (ht i), hb i]

end SHE.HeatTorusKernel
