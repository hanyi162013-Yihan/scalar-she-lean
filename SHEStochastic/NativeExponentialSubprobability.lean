module

public import SHEStochastic.NativeBoundedExponential
public import SHEStochastic.NativeEnergyLocalization

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHEStochastic.NativeExponentialSubprobability
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal Topology
open NativeExponential

variable {Ω C ι : Type*} [MeasurableSpace Ω] [Countable ι] [DecidableEq ι]
  [NormedAddCommGroup C] [InnerProductSpace ℝ C] [CompleteSpace C]
  [MeasurableSpace C] [BorelSpace C] [SecondCountableTopology C]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {H : ℝ≥0}

local notation "νin" => FiniteScalarIto.inputMeasure F μ H

theorem eLpNorm_one_eq_integral (P : FiniteScalarIto.Family F μ H ι) (e : HilbertBasis ι ℝ C)
    (a : ℝ) (u : Lp C 2 νin) (hi : Integrable (density P e a u) μ) :
    eLpNorm (density P e a u) 1 μ = ENNReal.ofReal (∫ ω, density P e a u ω ∂μ) := by
  rw [eLpNorm_one_eq_lintegral_enorm hi.aestronglyMeasurable,
    ← ofReal_integral_norm_eq_lintegral_enorm hi]
  congr 1
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun ω ↦ Real.norm_of_nonneg (Real.exp_pos _).le

/-- For every native predictable L2 input, its positive exponential has
finite expectation at most one. The general Novikov hypothesis is not
needed for this direction. -/
theorem integrable_and_le_one (P : FiniteScalarIto.Family F μ H ι) (e : HilbertBasis ι ℝ C)
    (a : ℝ) (u : Lp C 2 νin) :
    Integrable (density P e a u) μ ∧ (∫ ω, density P e a u ω ∂μ) ≤ 1 := by
  obtain ⟨U, hcap, hlim⟩ := NativeEnergyLocalization.exists_sequence e u
  have hb (n : ℕ) : ∀ᵐ ω ∂μ, NativeEnergy.energy (U n) ω ≤ (n : ℝ) :=
    (hcap n).mono fun ω hω ↦ hω.trans (min_le_right _ _)
  have hi (n : ℕ) : Integrable (density P e a (U n)) μ :=
    (NativeBoundedExponential.bounded_energy P e a (U n) (n : ℝ) (Nat.cast_nonneg _) (hb n)).1.integrable
      (by norm_num)
  have he (n : ℕ) : (∫ ω, density P e a (U n) ω ∂μ) = 1 :=
    (NativeBoundedExponential.bounded_energy P e a (U n) (n : ℝ) (Nat.cast_nonneg _) (hb n)).2.1
  have hn (n : ℕ) : eLpNorm (density P e a (U n)) 1 μ ≤ 1 := by
    rw [eLpNorm_one_eq_integral P e a (U n) (hi n), he n, ENNReal.ofReal_one]
  obtain ⟨ns, hns⟩ := NativeBoundedExponential.exists_density_ae_subsequence P e a hlim
  have hconv := tendstoInMeasure_of_tendsto_ae (fun k ↦ (hi (ns k)).aestronglyMeasurable) hns
  have hn' : eLpNorm (density P e a u) 1 μ ≤ 1 := eLpNorm_le_of_tendstoInMeasure
    (Filter.Eventually.of_forall fun k ↦ hn (ns k)) hconv (fun k ↦ (hi (ns k)).aestronglyMeasurable)
  have hgLp : MemLp (density P e a u) 1 μ := hn'.trans_lt (by simp)
  have hg := hgLp.integrable (by norm_num)
  refine ⟨hg, ?_⟩
  rw [eLpNorm_one_eq_integral P e a u hg] at hn'
  exact (ENNReal.ofReal_le_ofReal_iff (by norm_num : (0 : ℝ) ≤ 1)).mp (by simpa using hn')

end SHEStochastic.NativeExponentialSubprobability
