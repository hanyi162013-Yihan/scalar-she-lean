module

public import SHEStochastic.NativeBoundedExponential
public import SHEStochastic.NativeSimplePastExponential

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHEStochastic.NativePastExponential
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal Topology
open NativeExponential

variable {Ω C ι : Type*} [MeasurableSpace Ω] [Countable ι] [DecidableEq ι]
  [NormedAddCommGroup C] [InnerProductSpace ℝ C] [CompleteSpace C]
  [MeasurableSpace C] [BorelSpace C] [SecondCountableTopology C]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {H : ℝ≥0}

local notation "νin" => FiniteScalarIto.inputMeasure F μ H
local notation "emb" => HilbertSimpleInputs.embedding F μ H

/-- A bounded-energy predictable exponential supported after time `s`
has conditional mean one in the ENTIRE original past sigma algebra. -/
theorem conditional_mean_one_of_unit (P : FiniteScalarIto.Family F μ H ι) (e : HilbertBasis ι ℝ C)
    (a : ℝ) (s : ℝ≥0) (hsH : s ≤ H) (u : Lp C 2 νin)
    (hus : ∀ᵐ p ∂νin, p.1 ≤ s → u p = 0) (K : ℝ) (hK : 0 ≤ K)
    (hu : ∀ᵐ ω ∂μ, NativeEnergy.energy u ω ≤ K) (v : C) (hv : ‖v‖ = 1) :
    μ[density P e a u | F s] =ᵐ[μ] fun _ ↦ 1 := by
  obtain ⟨V, hstart, hcap, hlim⟩ :=
    NativeCappedApproximation.exists_sequence_after e s hsH u hus K hK hu
  have hLp (n : ℕ) : MemLp (density P e a (emb (V n))) 2 μ :=
    (simple_square_bound P e a (V n) v hv K (Filter.Eventually.of_forall (hcap n))).1
  have hbound (n : ℕ) : (∫ ω, density P e a (emb (V n)) ω ^ 2 ∂μ) ≤ Real.exp (a ^ 2 * K) :=
    (simple_square_bound P e a (V n) v hv K (Filter.Eventually.of_forall (hcap n))).2
  have hg := (NativeBoundedExponential.bounded_energy P e a u K hK hu).1
  obtain ⟨ns, hns⟩ := NativeBoundedExponential.exists_density_ae_subsequence P e a hlim
  have hconv := tendstoInMeasure_of_tendsto_ae
    (fun k ↦ (hLp (ns k)).aestronglyMeasurable) hns
  have hset (A : Set Ω) (hA : MeasurableSet[F s] A) (n : ℕ) :
      (∫ ω in A, density P e a (emb (V n)) ω ∂μ) = ∫ _ in A, (1 : ℝ) ∂μ := by
    rw [← setIntegral_condExp (F.le s) (hLp n |>.integrable (by norm_num)) hA]
    exact integral_congr_ae (ae_restrict_of_ae
      (NativeSimplePastExponential.conditional_mean_one P e (V n) s (hstart n) v hv a))
  have hlimit (A : Set Ω) (hA : MeasurableSet[F s] A) :
      (∫ ω in A, density P e a u ω ∂μ) = ∫ _ in A, (1 : ℝ) ∂μ := by
    have ht := MathFin.tendsto_setIntegral_of_tendstoInMeasure_of_sq_bound
      (fun k ↦ hLp (ns k)) (fun k ↦ hbound (ns k))
      (hg.mono_exponent (by norm_num)) hconv A
    simp only [hset A hA] at ht
    exact tendsto_nhds_unique ht tendsto_const_nhds
  apply Filter.EventuallyEq.symm
  exact ae_eq_condExp_of_forall_setIntegral_eq (F.le s) (hg.integrable (by norm_num))
    (fun _ _ _ ↦ (integrable_const (1 : ℝ)).integrableOn)
    (fun A hA _ ↦ (hlimit A hA).symm) stronglyMeasurable_const.aestronglyMeasurable

theorem conditional_mean_one (P : FiniteScalarIto.Family F μ H ι) (e : HilbertBasis ι ℝ C)
    (a : ℝ) (s : ℝ≥0) (hsH : s ≤ H) (u : Lp C 2 νin)
    (hus : ∀ᵐ p ∂νin, p.1 ≤ s → u p = 0) (K : ℝ) (hK : 0 ≤ K)
    (hu : ∀ᵐ ω ∂μ, NativeEnergy.energy u ω ≤ K) :
    μ[density P e a u | F s] =ᵐ[μ] fun _ ↦ 1 := by
  classical
  rcases subsingleton_or_nontrivial C with hC | hC
  · letI := hC
    letI : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
    have hu0 : u = 0 := Lp.ext (Filter.Eventually.of_forall fun _ ↦ Subsingleton.elim _ _)
    rw [hu0]
    have hh := condExp_congr_ae (m := F s) (density_zero P e a)
    rw [condExp_const (F.le s) (1 : ℝ)] at hh
    exact hh
  · letI := hC
    obtain ⟨v, hv⟩ := exists_norm_eq C (zero_le_one : (0 : ℝ) ≤ 1)
    exact conditional_mean_one_of_unit P e a s hsH u hus K hK hu v hv

end SHEStochastic.NativePastExponential
