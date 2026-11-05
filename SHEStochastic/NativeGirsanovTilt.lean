module

public import SHEStochastic.NativeCrossEnergy
public import SHEStochastic.NativeBoundedExponential

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHEStochastic.NativeGirsanovTilt
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
open NativeExponential NativeCrossEnergy

variable {Ω C ι : Type*} [MeasurableSpace Ω] [Countable ι] [DecidableEq ι]
  [NormedAddCommGroup C] [InnerProductSpace ℝ C] [CompleteSpace C]
  [MeasurableSpace C] [BorelSpace C] [SecondCountableTopology C]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {H : ℝ≥0}

local notation "νin" => FiniteScalarIto.inputMeasure F μ H

def shift (P : FiniteScalarIto.Family F μ H ι) (e : HilbertBasis ι ℝ C)
    (u v : Lp C 2 νin) (ω : Ω) : ℝ := FiniteCylindricalIto.rawIntegral P.toCoordinates e v ω + cross v u ω

theorem shift_stronglyMeasurable (P : FiniteScalarIto.Family F μ H ι) (e : HilbertBasis ι ℝ C)
    (u v : Lp C 2 νin) : StronglyMeasurable (shift P e u v) :=
  (Lp.stronglyMeasurable _).add (NativeCrossEnergy.stronglyMeasurable v u)

def measure (P : FiniteScalarIto.Family F μ H ι) (e : HilbertBasis ι ℝ C)
    (u : Lp C 2 νin) : Measure Ω := μ.withDensity (fun ω ↦ ENNReal.ofReal (density P e (-1) u ω))

theorem integral_change (P : FiniteScalarIto.Family F μ H ι) (e : HilbertBasis ι ℝ C)
    (u : Lp C 2 νin) (f : Ω → ℝ) :
    (∫ ω, f ω ∂measure P e u) = ∫ ω, density P e (-1) u ω * f ω ∂μ := by
  have hpos (ω : Ω) : 0 ≤ density P e (-1) u ω := (Real.exp_pos _).le
  simpa only [measure, ENNReal.toReal_ofReal (hpos _), smul_eq_mul] using
    integral_withDensity_eq_integral_toReal_smul
      (NativeExponential.stronglyMeasurable P e (-1) u).measurable.ennreal_ofReal
      (Filter.Eventually.of_forall fun _ ↦ ENNReal.ofReal_lt_top) f

theorem integrable_change_iff (P : FiniteScalarIto.Family F μ H ι) (e : HilbertBasis ι ℝ C)
    (u : Lp C 2 νin) (f : Ω → ℝ) :
    Integrable f (measure P e u) ↔ Integrable (fun ω ↦ density P e (-1) u ω * f ω) μ := by
  have hpos (ω : Ω) : 0 ≤ density P e (-1) u ω := (Real.exp_pos _).le
  simpa only [measure, ENNReal.toReal_ofReal (hpos _), smul_eq_mul] using
    (integrable_withDensity_iff_integrable_smul'
      (NativeExponential.stronglyMeasurable P e (-1) u).measurable.ennreal_ofReal
      (Filter.Eventually.of_forall fun _ ↦ ENNReal.ofReal_lt_top) (g := f))

theorem setIntegral_change (P : FiniteScalarIto.Family F μ H ι) (e : HilbertBasis ι ℝ C)
    (u : Lp C 2 νin) (f : Ω → ℝ) (A : Set Ω) (hA : MeasurableSet A) :
    (∫ ω in A, f ω ∂measure P e u) = ∫ ω in A, density P e (-1) u ω * f ω ∂μ := by
  rw [measure, restrict_withDensity hA]
  have hpos (ω : Ω) : 0 ≤ density P e (-1) u ω := (Real.exp_pos _).le
  simpa only [ENNReal.toReal_ofReal (hpos _), smul_eq_mul] using
    integral_withDensity_eq_integral_toReal_smul (μ := μ.restrict A)
      (NativeExponential.stronglyMeasurable P e (-1) u).measurable.ennreal_ofReal
      (Filter.Eventually.of_forall fun _ ↦ ENNReal.ofReal_lt_top) f

theorem probability (P : FiniteScalarIto.Family F μ H ι) (e : HilbertBasis ι ℝ C)
    (u : Lp C 2 νin) (K : ℝ) (hK : 0 ≤ K)
    (hu : ∀ᵐ ω ∂μ, NativeEnergy.energy u ω ≤ K) : IsProbabilityMeasure (measure P e u) := by
  obtain ⟨hLp, hmean, _⟩ := NativeBoundedExponential.bounded_energy P e (-1) u K hK hu
  have hi := hLp.integrable (by norm_num)
  constructor
  rw [measure, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal hi
      (Filter.Eventually.of_forall fun ω ↦ (Real.exp_pos _).le), hmean]
  simp

theorem tilt_identity (P : FiniteScalarIto.Family F μ H ι) (e : HilbertBasis ι ℝ C)
    (u v : Lp C 2 νin) (a : ℝ) :
    (fun ω ↦ density P e (-1) u ω * Real.exp (a * shift P e u v ω)) =ᵐ[μ]
      (fun ω ↦ Real.exp (a ^ 2 * NativeEnergy.energy v ω / 2) * density P e 1 (a • v - u) ω) := by
  letI : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
  have hI : (FiniteCylindricalIto.rawIntegral P.toCoordinates e (a • v - u) : Ω → ℝ) =ᵐ[μ]
      (fun ω ↦ a * FiniteCylindricalIto.rawIntegral P.toCoordinates e v ω - FiniteCylindricalIto.rawIntegral P.toCoordinates e u ω) := by
    rw [map_sub, map_smul]
    filter_upwards [Lp.coeFn_sub (a • FiniteCylindricalIto.rawIntegral P.toCoordinates e v)
      (FiniteCylindricalIto.rawIntegral P.toCoordinates e u), Lp.coeFn_smul a (FiniteCylindricalIto.rawIntegral P.toCoordinates e v)]
      with ω hs hm
    rw [hs, Pi.sub_apply, hm, Pi.smul_apply, smul_eq_mul]
  filter_upwards [hI, energy_combination v u a] with ω hIω hEω
  change Real.exp (-1 * FiniteCylindricalIto.rawIntegral P.toCoordinates e u ω -
      (-1 : ℝ) ^ 2 * NativeEnergy.energy u ω / 2) *
    Real.exp (a * (FiniteCylindricalIto.rawIntegral P.toCoordinates e v ω + cross v u ω)) =
      Real.exp (a ^ 2 * NativeEnergy.energy v ω / 2) *
        Real.exp (1 * FiniteCylindricalIto.rawIntegral P.toCoordinates e (a • v - u) ω -
          (1 : ℝ) ^ 2 * NativeEnergy.energy (a • v - u) ω / 2)
  rw [hIω, hEω, ← Real.exp_add, ← Real.exp_add]
  congr 1
  ring

theorem tilt_identity_of_energy (P : FiniteScalarIto.Family F μ H ι) (e : HilbertBasis ι ℝ C)
    (u v : Lp C 2 νin) (a q : ℝ) (hv : NativeEnergy.energy v =ᵐ[μ] fun _ ↦ q) :
    (fun ω ↦ density P e (-1) u ω * Real.exp (a * shift P e u v ω)) =ᵐ[μ]
      (fun ω ↦ Real.exp (a ^ 2 * q / 2) * density P e 1 (a • v - u) ω) := by
  filter_upwards [tilt_identity P e u v a, hv] with ω hω hvω
  change density P e (-1) u ω * Real.exp (a * shift P e u v ω) = _
  rw [hω, hvω]

/-- The shifted terminal observation has the Gaussian MGF under the
actual exponential measure whenever its original time energy is
deterministic. No Girsanov or Ito formula is assumed. -/
theorem mgf (P : FiniteScalarIto.Family F μ H ι) (e : HilbertBasis ι ℝ C)
    (u v : Lp C 2 νin) (K : ℝ) (hK : 0 ≤ K)
    (hu : ∀ᵐ ω ∂μ, NativeEnergy.energy u ω ≤ K)
    (q : ℝ) (hq : 0 ≤ q) (hv : NativeEnergy.energy v =ᵐ[μ] fun _ ↦ q) (a : ℝ) :
    Integrable (fun ω ↦ Real.exp (a * shift P e u v ω)) (measure P e u) ∧
      (∫ ω, Real.exp (a * shift P e u v ω) ∂measure P e u) = Real.exp (a ^ 2 * q / 2) := by
  letI : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
  have hc : ∀ᵐ ω ∂μ, NativeEnergy.energy (a • v - u) ω ≤ 2 * a ^ 2 * q + 2 * K := by
    filter_upwards [energy_combination_le v u a, hv, hu] with ω he hqω huω
    rw [hqω] at he
    exact he.trans (by linarith)
  obtain ⟨hLp, hmean, _⟩ := NativeBoundedExponential.bounded_energy P e 1 (a • v - u)
    (2 * a ^ 2 * q + 2 * K) (by positivity) hc
  have he : (fun ω ↦ density P e (-1) u ω * Real.exp (a * shift P e u v ω)) =ᵐ[μ]
      (fun ω ↦ Real.exp (a ^ 2 * q / 2) * density P e 1 (a • v - u) ω) := by
    filter_upwards [tilt_identity P e u v a, hv] with ω hω hvω
    change density P e (-1) u ω * Real.exp (a * shift P e u v ω) = _
    rw [hω, hvω]
  have hi := ((hLp.integrable (by norm_num)).const_mul (Real.exp (a ^ 2 * q / 2))).congr he.symm
  refine ⟨(integrable_change_iff P e u _).mpr hi, ?_⟩
  rw [integral_change, integral_congr_ae he, integral_const_mul, hmean, mul_one]

theorem gaussian_law (P : FiniteScalarIto.Family F μ H ι) (e : HilbertBasis ι ℝ C)
    (u v : Lp C 2 νin) (K : ℝ) (hK : 0 ≤ K)
    (hu : ∀ᵐ ω ∂μ, NativeEnergy.energy u ω ≤ K)
    (q : ℝ≥0) (hv : NativeEnergy.energy v =ᵐ[μ] fun _ ↦ (q : ℝ)) :
    HasLaw (shift P e u v) (gaussianReal 0 q) (measure P e u) := by
  letI : IsProbabilityMeasure (measure P e u) := probability P e u K hK hu
  have hZ := (shift_stronglyMeasurable P e u v).measurable
  refine ⟨hZ.aemeasurable, ?_⟩
  apply Eq.symm
  apply MathFin.measure_eq_of_mgf_id_eq (fun b ↦ integrable_exp_mul_gaussianReal b)
  funext b
  change (∫ z : ℝ, Real.exp (b * z) ∂gaussianReal 0 q) =
    ∫ z : ℝ, Real.exp (b * z) ∂(measure P e u).map (shift P e u v)
  rw [integral_map hZ.aemeasurable (by fun_prop)]
  calc
    _ = Real.exp ((q : ℝ) * b ^ 2 / 2) := by
      change ProbabilityTheory.mgf id (gaussianReal 0 q) b = _
      rw [mgf_id_gaussianReal]
      simp
    _ = _ := by
      rw [(mgf P e u v K hK hu q q.coe_nonneg hv b).2]
      congr 1
      ring

end SHEStochastic.NativeGirsanovTilt
