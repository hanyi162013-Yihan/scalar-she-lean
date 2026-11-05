module

public import SHEStochastic.NativeExponential
public import SHEStochastic.HilbertSimplePastGaussian

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHEStochastic.NativeSimplePastExponential
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
open FilteredSimplePartition HilbertSimpleGaussian HilbertSimplePastGaussian

variable {Ω C ι : Type*} [MeasurableSpace Ω] [Countable ι] [DecidableEq ι]
  [NormedAddCommGroup C] [InnerProductSpace ℝ C] [CompleteSpace C]
  [MeasurableSpace C] [BorelSpace C] [SecondCountableTopology C]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {H : ℝ≥0}

/-- The existing native exponential model with the original past at
time `s` retained throughout the cells before the support begins. -/
def model (P : FiniteScalarIto.Family F μ H ι) (e : HilbertBasis ι ℝ C)
    (V : HilbertSimpleInputs.bounded (E := C) F H) (s : ℝ≥0)
    (hVs : ∀ p ∈ V.val.value.support, s ≤ p.1) (v : C) (hv : ‖v‖ = 1) :
    DiscreteGaussianExponential.Model (pastGrid V s) μ where
  increment := cellVersion P e V
  variance := HilbertSimpleGaussian.variance V
  increment_adapted k := (cellVersion_measurable P e V k).mono (F.mono (le_max_right _ _))
  variance_adapted k :=
    (((stronglyMeasurable_marshalMult F H V.val k).norm.pow 2).const_mul _).mono
      (F.mono (le_max_right _ _))
  variance_nonneg k ω := mul_nonneg (NNReal.coe_nonneg _) (sq_nonneg _)
  exp_integrable := (NativeSimpleExponential.model P e V v hv).exp_integrable
  normalized k a := by
    by_cases hsk : s ≤ marshalPart F H V.val k
    · rw [pastGrid_apply, max_eq_right hsk]
      have hh := (NativeSimpleExponential.model P e V v hv).normalized k a
      rw [gridFiltration_apply, Nat.zero_add] at hh
      exact hh
    · have hk := lt_of_not_ge hsk
      have hzero : cellVersion P e V k =ᵐ[μ] fun _ ↦ 0 := by
        have hz : (cellIntegral P e V k : Ω → ℝ) =ᵐ[μ] fun _ ↦ 0 := by
          rw [cellIntegral_zero_before P e V s hVs hk]
          exact Lp.coeFn_zero ℝ 2 μ
        exact (cellVersion_ae P e V k).symm.trans hz
      have hrho : (fun ω ↦ Real.exp (a * cellVersion P e V k ω -
          a ^ 2 * HilbertSimpleGaussian.variance V k ω / 2)) =ᵐ[μ] fun _ ↦ 1 := by
        filter_upwards [hzero] with ω hω
        change Real.exp (a * cellVersion P e V k ω -
          a ^ 2 * HilbertSimpleGaussian.variance V k ω / 2) = 1
        rw [hω]
        simp only [HilbertSimpleGaussian.variance, coefficient_zero_before V s hVs hk,
          norm_zero, zero_pow two_ne_zero, mul_zero, zero_div, sub_zero, Real.exp_zero]
      have hh := condExp_congr_ae (m := pastGrid V s k) hrho
      rw [condExp_const ((pastGrid V s).le k) (1 : ℝ)] at hh
      exact hh

theorem conditional_mean_one (P : FiniteScalarIto.Family F μ H ι) (e : HilbertBasis ι ℝ C)
    (V : HilbertSimpleInputs.bounded (E := C) F H) (s : ℝ≥0)
    (hVs : ∀ p ∈ V.val.value.support, s ≤ p.1) (v : C) (hv : ‖v‖ = 1) (a : ℝ) :
    μ[NativeExponential.density P e a (HilbertSimpleInputs.embedding F μ H V) | F s] =ᵐ[μ]
      fun _ ↦ 1 := by
  let M := model P e V s hVs v hv
  let N := (marshalEndpoints F H V.val).card - 1
  have hN : marshalPart F H V.val N = H := marshalPart_card_sub_one F H V.val V.property
  have he : M.exponential a N =ᵐ[μ]
      NativeExponential.density P e a (HilbertSimpleInputs.embedding F μ H V) := by
    have hm : M.exponential a N = (NativeSimpleExponential.model P e V v hv).exponential a N := rfl
    rw [hm]
    exact (NativeSimpleExponential.exponential_ae P e V v hv N hN a).trans
      (NativeExponential.simple_ae P e a V).symm
  have hh := (M.martingale a).2 0 N (Nat.zero_le N)
  have hgrid : pastGrid V s 0 = F s := by
    rw [pastGrid_apply, marshalPart_zero F H V.val V.property, max_eq_left (zero_le : 0 ≤ s)]
  rw [hgrid] at hh
  have hzero : M.exponential a 0 = (fun _ ↦ 1) := by
    funext ω
    simp [DiscreteGaussianExponential.Model.exponential,
      DiscreteGaussianExponential.Model.sumIncrement, DiscreteGaussianExponential.Model.sumVariance]
  rw [hzero] at hh
  exact (condExp_congr_ae he).symm.trans hh

end SHEStochastic.NativeSimplePastExponential
