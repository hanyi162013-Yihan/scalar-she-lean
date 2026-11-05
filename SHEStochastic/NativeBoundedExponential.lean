module

public import SHEStochastic.NativeCappedApproximation
public import SHEStochastic.NativeExponential
public import MathFin.Foundations.GirsanovPredictableTheta
public import MathFin.Foundations.UnifIntegrableL2

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHEStochastic.NativeBoundedExponential
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal Topology
open FilteredSimplePartition NativeExponential

variable {Ω C ι : Type*} [MeasurableSpace Ω] [Countable ι] [DecidableEq ι]
  [NormedAddCommGroup C] [InnerProductSpace ℝ C] [CompleteSpace C]
  [MeasurableSpace C] [BorelSpace C] [SecondCountableTopology C]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {H : ℝ≥0}

local notation "νin" => FiniteScalarIto.inputMeasure F μ H
local notation "emb" => HilbertSimpleInputs.embedding F μ H

/-- A common almost-everywhere subsequence for the stochastic integral
and time energy gives convergence of the actual exponential densities. -/
theorem exists_density_ae_subsequence (P : FiniteScalarIto.Family F μ H ι)
    (e : HilbertBasis ι ℝ C) (a : ℝ) {un : ℕ → Lp C 2 νin} {u : Lp C 2 νin}
    (h : Filter.Tendsto un Filter.atTop (𝓝 u)) :
    ∃ ns : ℕ → ℕ, ∀ᵐ ω ∂μ, Filter.Tendsto
      (fun k ↦ density P e a (un (ns k)) ω) Filter.atTop (𝓝 (density P e a u ω)) := by
  letI : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
  have hi := tendstoInMeasure_of_tendsto_Lp
    (((FiniteCylindricalIto.rawIntegral P.toCoordinates e).continuous.tendsto u).comp h)
  have hb := NativeEnergy.tendstoInMeasure_energy h
  obtain ⟨ns, _, his, hbs⟩ := MathFin.exists_subseq_tendsto_ae₂ hi hb id Filter.tendsto_id
  refine ⟨ns, ?_⟩
  filter_upwards [his, hbs] with ω hiω hbω
  simp only [id_eq] at hiω hbω
  exact (Real.continuous_exp.tendsto _).comp
    ((hiω.const_mul a).sub ((hbω.const_mul (a ^ 2)).div_const 2))

/-- Mean one for arbitrary predictable native Hilbert inputs with an
almost-sure deterministic bound on total energy. The proof uses capped
simple approximation, the native cell identities, Fatou and Vitali. -/
theorem mean_one (P : FiniteScalarIto.Family F μ H ι) (e : HilbertBasis ι ℝ C)
    (a : ℝ) (u : Lp C 2 νin) (K : ℝ) (hK : 0 ≤ K)
    (hu : ∀ᵐ ω ∂μ, NativeEnergy.energy u ω ≤ K) (v : C) (hv : ‖v‖ = 1) :
    MemLp (density P e a u) 2 μ ∧ (∫ ω, density P e a u ω ∂μ) = 1 := by
  classical
  obtain ⟨V, hcap, hlim⟩ := NativeCappedApproximation.exists_sequence e u K hK hu
  have hLp (n : ℕ) : MemLp (density P e a (emb (V n))) 2 μ :=
    (simple_square_bound P e a (V n) v hv K (Filter.Eventually.of_forall (hcap n))).1
  have hbound (n : ℕ) : (∫ ω, density P e a (emb (V n)) ω ^ 2 ∂μ) ≤ Real.exp (a ^ 2 * K) :=
    (simple_square_bound P e a (V n) v hv K (Filter.Eventually.of_forall (hcap n))).2
  obtain ⟨ns, hns⟩ := exists_density_ae_subsequence P e a hlim
  have hg : MemLp (density P e a u) 2 μ :=
    MathFin.memLp_two_of_subseq_ae_of_sq_bound hLp
      (fun n ↦ (NativeExponential.stronglyMeasurable P e a (emb (V n))).measurable)
      hbound ⟨ns, hns⟩
  refine ⟨hg, ?_⟩
  have hconv := tendstoInMeasure_of_tendsto_ae
    (fun k ↦ (hLp (ns k)).aestronglyMeasurable) hns
  have hmean (n : ℕ) : (∫ ω, density P e a (emb (V n)) ω ∂μ) = 1 :=
    (simple_mean_one P e a (V n) v hv).2
  have ht := MathFin.tendsto_setIntegral_of_tendstoInMeasure_of_sq_bound
    (fun k ↦ hLp (ns k)) (fun k ↦ hbound (ns k))
    (hg.mono_exponent (by norm_num)) hconv Set.univ
  simp only [Measure.restrict_univ, hmean] at ht
  exact tendsto_nhds_unique ht tendsto_const_nhds

theorem square_integral_le (P : FiniteScalarIto.Family F μ H ι) (e : HilbertBasis ι ℝ C)
    (a : ℝ) (u : Lp C 2 νin) (K : ℝ) (hK : 0 ≤ K)
    (hu : ∀ᵐ ω ∂μ, NativeEnergy.energy u ω ≤ K) (v : C) (hv : ‖v‖ = 1) :
    (∫ ω, density P e a u ω ^ 2 ∂μ) ≤ Real.exp (a ^ 2 * K) := by
  have hs := (mean_one P e a u K hK hu v hv).1.integrable_sq
  obtain ⟨hm, he⟩ := mean_one P e (2 * a) u K hK hu v hv
  have hi := (hm.integrable (by norm_num)).const_mul (Real.exp (a ^ 2 * K))
  have hb : ∀ᵐ ω ∂μ, density P e a u ω ^ 2 ≤
      Real.exp (a ^ 2 * K) * density P e (2 * a) u ω := by
    filter_upwards [hu] with ω hω
    dsimp [density]
    rw [pow_two, ← Real.exp_add, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_left hω (sq_nonneg a)]
  have hh := integral_mono_ae hs hi hb
  rw [integral_const_mul, he, mul_one] at hh
  exact hh

/-- Complete bounded-energy endpoint, including the zero Hilbert space.
No unit vector is an input to the resulting theorem. -/
theorem bounded_energy (P : FiniteScalarIto.Family F μ H ι) (e : HilbertBasis ι ℝ C)
    (a : ℝ) (u : Lp C 2 νin) (K : ℝ) (hK : 0 ≤ K)
    (hu : ∀ᵐ ω ∂μ, NativeEnergy.energy u ω ≤ K) :
    MemLp (density P e a u) 2 μ ∧ (∫ ω, density P e a u ω ∂μ) = 1 ∧
      (∫ ω, density P e a u ω ^ 2 ∂μ) ≤ Real.exp (a ^ 2 * K) := by
  classical
  rcases subsingleton_or_nontrivial C with hC | hC
  · letI := hC
    letI : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
    have hu0 : u = 0 := Lp.ext (Filter.Eventually.of_forall fun _ ↦ Subsingleton.elim _ _)
    have hρ : density P e a u =ᵐ[μ] (fun _ ↦ 1) := by
      rw [hu0]
      exact density_zero P e a
    refine ⟨(memLp_congr_ae hρ).mpr (memLp_const (1 : ℝ)), ?_, ?_⟩
    · rw [integral_congr_ae hρ]
      simp
    · have he : (fun ω ↦ density P e a u ω ^ 2) =ᵐ[μ] (fun _ ↦ 1) :=
        hρ.mono fun ω hω ↦ by
          change density P e a u ω ^ 2 = 1
          change density P e a u ω = 1 at hω
          rw [hω, one_pow]
      rw [integral_congr_ae he]
      simpa using Real.one_le_exp (mul_nonneg (sq_nonneg a) hK)
  · letI := hC
    obtain ⟨v, hv⟩ := exists_norm_eq C (zero_le_one : (0 : ℝ) ≤ 1)
    obtain ⟨hLp, he⟩ := mean_one P e a u K hK hu v hv
    exact ⟨hLp, he, square_integral_le P e a u K hK hu v hv⟩

end SHEStochastic.NativeBoundedExponential
