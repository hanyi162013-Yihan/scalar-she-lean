module

public import SHEStochastic.NativeExponentialSubprobability
public import SHEStochastic.GeometricUniformIntegrability

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHEStochastic.NativeNovikov
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal Topology
open NativeExponential

/-- The elementary interpolation inequality behind Novikov's criterion. -/
theorem exp_geometric_bound (X E D θ : ℝ) (hD : 0 ≤ D) (hDE : D ≤ E)
    (hθ0 : 0 < θ) (hθ1 : θ < 1) :
    Real.exp (θ * X - θ ^ 2 * D / 2) ≤
      Real.exp (X - D / 2) ^ θ * Real.exp (E / 2) ^ (1 - θ) := by
  rw [← Real.exp_mul, ← Real.exp_mul, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hθD : θ * D ≤ E := (mul_le_of_le_one_left hD hθ1.le).trans hDE
  nlinarith [mul_nonneg (sub_nonneg.mpr hθ1.le) (sub_nonneg.mpr hθD)]

theorem enorm_exp_geometric_bound (X E D θ : ℝ) (hD : 0 ≤ D) (hDE : D ≤ E)
    (hθ0 : 0 < θ) (hθ1 : θ < 1) :
    ‖Real.exp (θ * X - θ ^ 2 * D / 2)‖ₑ ≤
      ‖Real.exp (X - D / 2)‖ₑ ^ θ * ‖Real.exp (E / 2)‖ₑ ^ (1 - θ) := by
  simp only [Real.enorm_eq_ofReal (Real.exp_pos _).le]
  rw [ENNReal.ofReal_rpow_of_pos (Real.exp_pos _),
    ENNReal.ofReal_rpow_of_pos (Real.exp_pos _),
    ← ENNReal.ofReal_mul (Real.rpow_nonneg (Real.exp_pos _).le _)]
  exact ENNReal.ofReal_le_ofReal (exp_geometric_bound X E D θ hD hDE hθ0 hθ1)

theorem one_le_of_interpolation {m M : ℝ} (hm : 0 ≤ m) (hM : 0 < M)
    (hbound : ∀ θ : ℝ, 0 < θ → θ < 1 → 1 ≤ m ^ θ * M ^ (1 - θ)) : 1 ≤ m := by
  have hmne : m ≠ 0 := by
    intro hz
    have hh := hbound (1 / 2) (by norm_num) (by norm_num)
    simp only [hz, Real.zero_rpow (by norm_num : (1 / 2 : ℝ) ≠ 0), zero_mul] at hh
    norm_num at hh
  have hmpos : 0 < m := lt_of_le_of_ne hm hmne.symm
  have hc : Continuous (fun θ : ℝ ↦ m ^ θ * M ^ (1 - θ)) := by fun_prop
  have ht : Filter.Tendsto (fun θ : ℝ ↦ m ^ θ * M ^ (1 - θ)) (𝓝[<] (1 : ℝ)) (𝓝 m) := by
    simpa only [sub_self, Real.rpow_zero, Real.rpow_one, mul_one] using
      (hc.tendsto (1 : ℝ)).mono_left nhdsWithin_le_nhds
  apply ge_of_tendsto ht
  filter_upwards [self_mem_nhdsWithin,
    (eventually_gt_nhds (zero_lt_one : (0 : ℝ) < 1)).filter_mono nhdsWithin_le_nhds]
    with θ hθ1 hθ0
  exact hbound θ hθ0 hθ1

variable {Ω C ι : Type*} [MeasurableSpace Ω] [Countable ι] [DecidableEq ι]
  [NormedAddCommGroup C] [InnerProductSpace ℝ C] [CompleteSpace C]
  [MeasurableSpace C] [BorelSpace C] [SecondCountableTopology C]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {H : ℝ≥0}

local notation "νin" => FiniteScalarIto.inputMeasure F μ H

/-- Below the Novikov endpoint, geometric interpolation supplies uniform
integrability of the localized densities. -/
theorem scaled_mean_one (P : FiniteScalarIto.Family F μ H ι) (e : HilbertBasis ι ℝ C)
    (a : ℝ) (u : Lp C 2 νin)
    (hNov : Integrable (fun ω ↦ Real.exp (a ^ 2 * NativeEnergy.energy u ω / 2)) μ)
    (θ : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < 1) :
    (∫ ω, density P e (θ * a) u ω ∂μ) = 1 := by
  obtain ⟨U, hcap, hlim⟩ := NativeEnergyLocalization.exists_sequence e u
  have hb (n : ℕ) : ∀ᵐ ω ∂μ, NativeEnergy.energy (U n) ω ≤ (n : ℝ) :=
    (hcap n).mono fun ω hω ↦ hω.trans (min_le_right _ _)
  have hi (n : ℕ) : Integrable (density P e a (U n)) μ :=
    (NativeBoundedExponential.bounded_energy P e a (U n) (n : ℝ) (Nat.cast_nonneg _) (hb n)).1.integrable
      (by norm_num)
  have hmean (b : ℝ) (n : ℕ) : (∫ ω, density P e b (U n) ω ∂μ) = 1 :=
    (NativeBoundedExponential.bounded_energy P e b (U n) (n : ℝ) (Nat.cast_nonneg _) (hb n)).2.1
  have hmass (n : ℕ) : (∫⁻ ω, ‖density P e a (U n) ω‖ₑ ∂μ) ≤ 1 := by
    rw [← eLpNorm_one_eq_lintegral_enorm (hi n).aestronglyMeasurable,
      NativeExponentialSubprobability.eLpNorm_one_eq_integral P e a (U n) (hi n),
      hmean a n, ENNReal.ofReal_one]
  have hdom (n : ℕ) : ∀ᵐ ω ∂μ, ‖density P e (θ * a) (U n) ω‖ₑ ≤
      ‖density P e a (U n) ω‖ₑ ^ θ *
        ‖Real.exp (a ^ 2 * NativeEnergy.energy u ω / 2)‖ₑ ^ (1 - θ) := by
    filter_upwards [hcap n] with ω hω
    have hD : 0 ≤ a ^ 2 * NativeEnergy.energy (U n) ω :=
      mul_nonneg (sq_nonneg _) (integral_nonneg fun _ ↦ sq_nonneg _)
    have hDE := mul_le_mul_of_nonneg_left (hω.trans (min_le_left _ _)) (sq_nonneg a)
    have hh := enorm_exp_geometric_bound
      (a * FiniteCylindricalIto.rawIntegral P.toCoordinates e (U n) ω)
      (a ^ 2 * NativeEnergy.energy u ω) (a ^ 2 * NativeEnergy.energy (U n) ω)
      θ hD hDE hθ0 hθ1
    have he : density P e (θ * a) (U n) ω =
        Real.exp (θ * (a * FiniteCylindricalIto.rawIntegral P.toCoordinates e (U n) ω) -
          θ ^ 2 * (a ^ 2 * NativeEnergy.energy (U n) ω) / 2) := by
      unfold density
      congr 1
      ring
    rw [he]
    exact hh
  have hui : UnifIntegrable (fun n ↦ density P e (θ * a) (U n)) 1 μ :=
    GeometricUniformIntegrability.of_geometric_bound
      (fun n ↦ (NativeExponential.stronglyMeasurable P e (θ * a) (U n)).aestronglyMeasurable)
      (fun n ↦ (hi n).aestronglyMeasurable.enorm) hmass hNov hθ0 hθ1 hdom
  have hg := (NativeExponentialSubprobability.integrable_and_le_one P e (θ * a) u).1
  obtain ⟨ns, hns⟩ := NativeBoundedExponential.exists_density_ae_subsequence P e (θ * a) hlim
  have hfn (k : ℕ) := (NativeExponentialSubprobability.integrable_and_le_one P e (θ * a) (U (ns k))).1
  have hconv := tendstoInMeasure_of_tendsto_ae (fun k ↦ (hfn k).aestronglyMeasurable) hns
  have hL1 := tendsto_Lp_finite_of_tendstoInMeasure le_rfl ENNReal.one_ne_top
    (fun k ↦ (hfn k).aestronglyMeasurable) (memLp_one_iff_integrable.mpr hg) (hui.comp ns) hconv
  have hnorm (k : ℕ) : eLpNorm (density P e (θ * a) (U (ns k)) - density P e (θ * a) u) 1 μ =
      ∫⁻ ω, ‖density P e (θ * a) (U (ns k)) ω - density P e (θ * a) u ω‖ₑ ∂μ :=
    eLpNorm_one_eq_lintegral_enorm ((hfn k).sub hg).aestronglyMeasurable
  have ht := tendsto_setIntegral_of_L1 (density P e (θ * a) u) hg.aestronglyMeasurable
    (Filter.Eventually.of_forall hfn) (by simpa only [hnorm] using hL1) Set.univ
  simp only [Measure.restrict_univ, hmean] at ht
  exact tendsto_nhds_unique ht tendsto_const_nhds

/-- The full native Novikov mean-one theorem, with only the ordinary
exponential-energy integrability condition. -/
theorem mean_one (P : FiniteScalarIto.Family F μ H ι) (e : HilbertBasis ι ℝ C)
    (a : ℝ) (u : Lp C 2 νin)
    (hNov : Integrable (fun ω ↦ Real.exp (a ^ 2 * NativeEnergy.energy u ω / 2)) μ) :
    Integrable (density P e a u) μ ∧ (∫ ω, density P e a u ω ∂μ) = 1 := by
  obtain ⟨hi, hle⟩ := NativeExponentialSubprobability.integrable_and_le_one P e a u
  refine ⟨hi, le_antisymm hle ?_⟩
  let m := ∫ ω, density P e a u ω ∂μ
  let M := ∫ ω, Real.exp (a ^ 2 * NativeEnergy.energy u ω / 2) ∂μ
  have hm : 0 ≤ m := integral_nonneg fun _ ↦ (Real.exp_pos _).le
  have hM1 : 1 ≤ M := by
    have hh := integral_mono (integrable_const (1 : ℝ)) hNov
      (fun ω ↦ Real.one_le_exp (div_nonneg
        (mul_nonneg (sq_nonneg _) (integral_nonneg fun _ ↦ sq_nonneg _)) (by norm_num)))
    simpa using hh
  have hM0 : 0 ≤ M := zero_le_one.trans hM1
  have hmass : (∫⁻ ω, ‖density P e a u ω‖ₑ ∂μ) = ENNReal.ofReal m := by
    rw [← eLpNorm_one_eq_lintegral_enorm hi.aestronglyMeasurable,
      NativeExponentialSubprobability.eLpNorm_one_eq_integral P e a u hi]
  have hmajor : (∫⁻ ω, ‖Real.exp (a ^ 2 * NativeEnergy.energy u ω / 2)‖ₑ ∂μ) = ENNReal.ofReal M := by
    rw [← ofReal_integral_norm_eq_lintegral_enorm hNov]
    congr 1
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun ω ↦ Real.norm_of_nonneg (Real.exp_pos _).le
  apply one_le_of_interpolation hm (zero_lt_one.trans_le hM1)
  intro θ hθ0 hθ1
  have hscaledI := (NativeExponentialSubprobability.integrable_and_le_one P e (θ * a) u).1
  have hscaled : (∫⁻ ω, ‖density P e (θ * a) u ω‖ₑ ∂μ) = 1 := by
    rw [← eLpNorm_one_eq_lintegral_enorm hscaledI.aestronglyMeasurable,
      NativeExponentialSubprobability.eLpNorm_one_eq_integral P e (θ * a) u hscaledI,
      scaled_mean_one P e a u hNov θ hθ0 hθ1, ENNReal.ofReal_one]
  have hdom : (∫⁻ ω, ‖density P e (θ * a) u ω‖ₑ ∂μ) ≤
      ∫⁻ ω, ‖density P e a u ω‖ₑ ^ θ *
        ‖Real.exp (a ^ 2 * NativeEnergy.energy u ω / 2)‖ₑ ^ (1 - θ) ∂μ := by
    apply lintegral_mono
    intro ω
    change ‖density P e (θ * a) u ω‖ₑ ≤ ‖density P e a u ω‖ₑ ^ θ *
      ‖Real.exp (a ^ 2 * NativeEnergy.energy u ω / 2)‖ₑ ^ (1 - θ)
    have hD : 0 ≤ a ^ 2 * NativeEnergy.energy u ω :=
      mul_nonneg (sq_nonneg _) (integral_nonneg fun _ ↦ sq_nonneg _)
    have hh := enorm_exp_geometric_bound
      (a * FiniteCylindricalIto.rawIntegral P.toCoordinates e u ω)
      (a ^ 2 * NativeEnergy.energy u ω) (a ^ 2 * NativeEnergy.energy u ω)
      θ hD le_rfl hθ0 hθ1
    have he : density P e (θ * a) u ω =
        Real.exp (θ * (a * FiniteCylindricalIto.rawIntegral P.toCoordinates e u ω) -
          θ ^ 2 * (a ^ 2 * NativeEnergy.energy u ω) / 2) := by
      unfold density
      congr 1
      ring
    rw [he]
    exact hh
  have hh := hdom.trans (GeometricUniformIntegrability.lintegral_geometric
    hi.aestronglyMeasurable.enorm hNov.aestronglyMeasurable.enorm hθ0 hθ1)
  rw [hscaled, hmass, hmajor, ENNReal.ofReal_rpow_of_nonneg hm hθ0.le,
    ENNReal.ofReal_rpow_of_nonneg hM0 (sub_nonneg.mpr hθ1.le),
    ← ENNReal.ofReal_mul (Real.rpow_nonneg hm θ)] at hh
  exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg (Real.rpow_nonneg hm _)
    (Real.rpow_nonneg hM0 _))).mp (by simpa only [ENNReal.ofReal_one] using hh)

end SHEStochastic.NativeNovikov
