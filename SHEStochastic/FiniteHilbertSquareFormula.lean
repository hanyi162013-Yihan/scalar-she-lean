module

public import SHEStochastic.FiniteOrthonormalSums
public import SHEStochastic.NativeSquareFormula

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
noncomputable section

namespace SHEStochastic.FiniteHilbertSquareFormula
open MeasureTheory ProbabilityTheory SHE SHE.PredictableL2 Filter
open scoped NNReal ENNReal

variable {Ω C E ι κ : Type*} [MeasurableSpace Ω] [Countable ι] [DecidableEq ι]
  [Fintype κ] [DecidableEq κ]
  [NormedAddCommGroup C] [InnerProductSpace ℝ C] [CompleteSpace C]
  [MeasurableSpace C] [BorelSpace C] [SecondCountableTopology C]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {H : ℝ≥0}

/-- Sum the already proved scalar square identities in orthonormal
output directions. The gradient row and its bracket comparison have no
dimension factor, even when output and noise spaces are different. -/
theorem exists_input (P : FiniteScalarIto.Family F μ H ι) (e : HilbertBasis ι ℝ C)
    (R : κ → Process (E := C) F μ H) (M : ℝ≥0)
    (hR : ∀ i, ∀ᵐ p ∂(energyMeasure μ H).trim (predictable_le_product F), ‖R i p‖ ≤ M)
    (v : κ → E) (hv : Orthonormal ℝ v) (X : κ → ℝ≥0 → Ω → ℝ)
    (hXa : ∀ i, StronglyAdapted F (X i))
    (hXp : ∀ i, StronglyMeasurable[F.predictable] (Function.uncurry (X i)))
    (hXc : ∀ i, ∀ᵐ ω ∂μ, ContinuousOn (fun t ↦ X i t ω) (Set.Icc 0 H))
    (hRep : ∀ i t, X i t =ᵐ[μ] (FiniteCylindricalIto.terminalIto P.toCoordinates e).integral
      (StoppedItoInputs.stop F μ H t (R i)))
    (D : Ω → ℝ) (hD : MemLp D 2 μ) (hD0 : ∀ ω, 0 ≤ D ω)
    (hb : ∀ᵐ ω ∂μ, ∀ t, ‖FiniteOrthonormalSums.value v (fun i ↦ X i t ω)‖ ≤ D ω) :
    ∃ V : Process (E := C) F μ H,
      V =ᵐ[energyMeasure μ H] (fun p ↦ ∑ i, X i p.1 p.2 • R i p) ∧
      (∀ᵐ ω ∂μ, ‖FiniteOrthonormalSums.value v (fun i ↦ X i H ω)‖ ^ 2 -
        ‖FiniteOrthonormalSums.value v (fun i ↦ X i 0 ω)‖ ^ 2 =
          2 * (FiniteCylindricalIto.terminalIto P.toCoordinates e).integral V ω +
            ∑ i, StochasticExponential.bracket F μ H (R i) ω) ∧
      ∀ᵐ ω ∂μ, StochasticExponential.bracket F μ H V ω ≤
        D ω ^ 2 * ∑ i, StochasticExponential.bracket F μ H (R i) ω := by
  let J := FiniteCylindricalIto.terminalIto P.toCoordinates e
  have hbi (i : κ) : ∀ᵐ ω ∂μ, ∀ t, |X i t ω| ≤ D ω := by
    filter_upwards [hb] with ω hω
    intro t
    exact (FiniteOrthonormalSums.coefficient_le v hv (fun i ↦ X i t ω) i).trans (hω t)
  let W (i : κ) := PredictableEnvelopeMultiplier.process (R i) M M.property (hR i)
    (Function.uncurry (X i)) (hXp i) D hD (PredictableEnvelopeMultiplier.path_bound (X i) D (hbi i))
  have hW (i : κ) : W i =ᵐ[energyMeasure μ H] (fun p ↦ X i p.1 p.2 • R i p) :=
    PredictableEnvelopeMultiplier.process_ae (R i) M M.property (hR i) _ (hXp i) D hD
      (PredictableEnvelopeMultiplier.path_bound (X i) D (hbi i))
  have hS (i : κ) := NativeSquareFormula.formula P e (R i) M M.property (hR i) (X i)
    (hXa i) (hXp i) (hXc i) (hRep i) D hD hD0 (hbi i)
  letI : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
  let V : Process (E := C) F μ H := ∑ i, W i
  have hV : V =ᵐ[energyMeasure μ H] (fun p ↦ ∑ i, X i p.1 p.2 • R i p) := by
    filter_upwards [ae_eq_of_ae_eq_trim (Lp.coeFn_finsetSum Finset.univ W), ae_all_iff.mpr hW] with p hs hp
    change V p = _ at hs
    rw [hs]
    simp only [Finset.sum_apply]
    exact Finset.sum_congr rfl (fun i _ ↦ hp i)
  have hJV : J.integral V =ᵐ[μ] (fun ω ↦ ∑ i, J.integral (W i) ω) := by
    change J.integral (∑ i, W i) =ᵐ[μ] _
    rw [map_sum]
    filter_upwards [Lp.coeFn_finsetSum Finset.univ (fun i ↦ J.integral (W i))] with ω hω
    change _ = _ at hω
    simpa only [Finset.sum_apply] using hω
  refine ⟨V, hV, ?_, ?_⟩
  · filter_upwards [ae_all_iff.mpr hS, hJV] with ω hs hj
    rw [FiniteOrthonormalSums.norm_sq v hv, FiniteOrthonormalSums.norm_sq v hv,
      ← Finset.sum_sub_distrib, hj]
    calc
      _ = ∑ i, (2 * J.integral (W i) ω + StochasticExponential.bracket F μ H (R i) ω) :=
        Finset.sum_congr rfl (fun i _ ↦ hs i)
      _ = _ := by rw [Finset.sum_add_distrib, Finset.mul_sum]
  · letI : MeasurableSpace (ℝ≥0 × Ω) :=
      (inferInstance : MeasurableSpace ℝ≥0).prod ‹MeasurableSpace Ω›
    have hi (i : κ) : Integrable (fun p : ℝ≥0 × Ω ↦ ‖R i p‖ ^ 2) (energyMeasure μ H) :=
      (memLp_of_memLp_trim (predictable_le_product F) (Lp.memLp (R i))).norm.integrable_sq
    have hiV := (memLp_of_memLp_trim (predictable_le_product F) (Lp.memLp V)).norm.integrable_sq
    have hs := (Measure.measurePreserving_swap (μ := μ) (ν := timeMeasure H)).quasiMeasurePreserving.ae hV
    filter_upwards [ae_all_iff.mpr (fun i ↦ (hi i).prod_left_ae), hiV.prod_left_ae,
      Measure.ae_ae_of_ae_prod hs, hb] with ω hiω hvω hr hbω
    change (∫ r, ‖V (r, ω)‖ ^ 2 ∂timeMeasure H) ≤
      D ω ^ 2 * ∑ i, (∫ r, ‖R i (r, ω)‖ ^ 2 ∂timeMeasure H)
    rw [← integral_finsetSum _ (fun i _ ↦ hiω i), ← integral_const_mul]
    apply integral_mono_ae hvω ((integrable_finsetSum _ (fun i _ ↦ hiω i)).const_mul (D ω ^ 2))
    filter_upwards [hr] with r hr
    change V (r, ω) = ∑ i, X i r ω • R i (r, ω) at hr
    rw [hr]
    have hh := FiniteOrthonormalSums.weighted_row_sq (fun i ↦ X i r ω) (fun i ↦ R i (r, ω))
    rw [← FiniteOrthonormalSums.norm_sq v hv] at hh
    exact hh.trans (mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (norm_nonneg _) (hbω r) 2) (Finset.sum_nonneg fun _ _ ↦ sq_nonneg _))

end SHEStochastic.FiniteHilbertSquareFormula
