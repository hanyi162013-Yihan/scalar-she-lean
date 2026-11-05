module

public import SHEStochastic.FiniteItoStochasticTerms

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
noncomputable section

namespace SHEStochastic.FiniteItoQuadraticTerms
open MeasureTheory ProbabilityTheory SHE SHE.PredictableL2 SHE.StoppedItoInputs SHE.GaussianItoTest
open MathFin.QuadraticVariationL2
open scoped NNReal ENNReal Topology

variable {Ω C : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup C] [InnerProductSpace ℝ C] [CompleteSpace C]
  [MeasurableSpace C] [BorelSpace C] [SecondCountableTopology C]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {H : ℝ≥0} {n : ℕ}

theorem bilinear_apply (B : State n →L[ℝ] State n →L[ℝ] ℝ) (x y : State n) :
    B x y = ∑ i : Fin n, ∑ j : Fin n, x i * y j * B
      (EuclideanSpace.basisFun (Fin n) ℝ i) (EuclideanSpace.basisFun (Fin n) ℝ j) := by
  have hx := FiniteItoStochasticTerms.linear_apply (B.flip y) x
  change B x y = ∑ i : Fin n, x i * B (EuclideanSpace.basisFun (Fin n) ℝ i) y at hx
  rw [hx]
  apply Finset.sum_congr rfl
  intro i hi
  rw [FiniteItoStochasticTerms.linear_apply (B (EuclideanSpace.basisFun (Fin n) ℝ i)) y,
    Finset.mul_sum]
  exact Finset.sum_congr rfl (fun j hj ↦ by ring)

def sum (Y : ℝ≥0 × Ω → State n) (G : ℝ → State n → ℝ) (m : ℕ) (ω : Ω) : ℝ :=
  ∑ k : Fin m, GaussianTaylor.hessian (G (unifPart H m k)) (Y (unifPart H m k, ω))
    (Y (unifPart H m (k + 1), ω) - Y (unifPart H m k, ω))
    (Y (unifPart H m (k + 1), ω) - Y (unifPart H m k, ω))

def energy (R : Fin n → Process (E := C) F μ H)
    (Y : ℝ≥0 × Ω → State n) (G : ℝ → State n → ℝ) (ω : Ω) : ℝ :=
  ∫ r, GaussianTaylorAverage.covarianceAction
    (fun i j ↦ inner ℝ (R i (r, ω)) (R j (r, ω)))
    (GaussianTaylor.hessian (G r) (Y (r, ω))) ∂timeMeasure H

/-- The finite-dimensional quadratic form is the sum of actual mixed
increment products, with the Hessian entries as weights. -/
theorem sum_ae (J : StandardTerminalIto (C := C) (E := ℝ) F μ H)
    (R : Fin n → Process (E := C) F μ H) (z : Ω → State n) (Y : ℝ≥0 × Ω → State n)
    (hRep : ∀ t : ℝ≥0, t ≤ H → (fun ω ↦ Y (t, ω)) =ᵐ[μ]
      (fun ω ↦ StandardFiniteIto.vectorIntegral F μ H J (z ω) R t ω)) (G : ℝ → State n → ℝ) (m : ℕ) :
    sum (H := H) Y G m =ᵐ[μ] (fun ω ↦ ∑ i : Fin n, ∑ j : Fin n,
      NativeWeightedCovariation.sum J (R i) (R j) (FiniteItoWeights.hessian Y G i j) m ω) := by
  filter_upwards [FiniteItoStochasticTerms.increment_rep J R z Y hRep m] with ω hω
  have he : sum (H := H) Y G m ω = ∑ k : Fin m, ∑ i : Fin n, ∑ j : Fin n,
      (Y (unifPart H m (k + 1), ω) - Y (unifPart H m k, ω)) i *
      (Y (unifPart H m (k + 1), ω) - Y (unifPart H m k, ω)) j *
      GaussianTaylor.hessian (G (unifPart H m k)) (Y (unifPart H m k, ω))
        (EuclideanSpace.basisFun (Fin n) ℝ i) (EuclideanSpace.basisFun (Fin n) ℝ j) :=
    Finset.sum_congr rfl (fun k hk ↦ bilinear_apply _ _ _)
  rw [he, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro k hk
  rw [hω k i, hω k j]
  dsimp [FiniteItoWeights.hessian]
  ring

theorem measurable_mixed_sum (J : StandardTerminalIto (C := C) (E := ℝ) F μ H)
    (u v : Process (E := C) F μ H) (w : ℝ≥0 → Ω → ℝ) (hw : StronglyAdapted F w) (m : ℕ) :
    StronglyMeasurable (NativeWeightedCovariation.sum J u v w m) := by
  apply Finset.stronglyMeasurable_fun_sum
  intro (k : Fin m) hk
  have hu := (Lp.stronglyMeasurable (J.integral (stop F μ H (unifPart H m (k + 1)) u))).sub
    (Lp.stronglyMeasurable (J.integral (stop F μ H (unifPart H m k) u)))
  have hv := (Lp.stronglyMeasurable (J.integral (stop F μ H (unifPart H m (k + 1)) v))).sub
    (Lp.stronglyMeasurable (J.integral (stop F μ H (unifPart H m k) v)))
  exact (((hw _).mono (F.le _)).mul hu).mul hv

/-- The weighted mixed density is integrable on the original product
space, by the L² row bounds and the bounded predictable weight. -/
theorem product_integrable (u v : Process (E := C) F μ H) (w : ℝ≥0 → Ω → ℝ)
    (hp : StronglyMeasurable[F.predictable] (Function.uncurry w))
    (B : ℝ) (hwb : ∀ t ω, |w t ω| ≤ B) :
    Integrable (fun p : ℝ≥0 × Ω ↦ w p.1 p.2 * inner ℝ (u p) (v p)) (energyMeasure μ H) := by
  have hu := memLp_of_memLp_trim (predictable_le_product F) (Lp.memLp u)
  have hv := memLp_of_memLp_trim (predictable_le_product F) (Lp.memLp v)
  have hi : Integrable (fun p : ℝ≥0 × Ω ↦ inner ℝ (u p) (v p)) (energyMeasure μ H) := by
    apply (hu.norm.integrable_mul hv.norm).mono'
      (((Lp.stronglyMeasurable u).mono (predictable_le_product F)).inner
        ((Lp.stronglyMeasurable v).mono (predictable_le_product F))).aestronglyMeasurable
    exact Filter.Eventually.of_forall fun p ↦ abs_real_inner_le_norm _ _
  have hm : StronglyMeasurable (fun p : ℝ≥0 × Ω ↦ w p.1 p.2) := by
    simpa only [Function.uncurry_def] using hp.mono (predictable_le_product F)
  exact hi.bdd_mul hm.aestronglyMeasurable (Filter.Eventually.of_forall fun p ↦ by
    simpa only [Real.norm_eq_abs] using hwb p.1 p.2)

/-- Finite summation commutes with the actual predictable row energy. -/
theorem energy_sum_ae (R : Fin n → Process (E := C) F μ H)
    (Y : ℝ≥0 × Ω → State n) (hY : StronglyMeasurable[F.predictable] Y)
    {a b : ℝ} {G dG : ℝ → State n → ℝ} (hG : RegularTest a b G dG) :
    energy R Y G =ᵐ[μ] (fun ω ↦ ∑ i : Fin n, ∑ j : Fin n,
      NativeWeightedCovariation.energy (R i) (R j) (FiniteItoWeights.hessian Y G i j) ω) := by
  obtain ⟨B, hB, hb⟩ := FiniteItoWeights.hessian_bound Y hG
  have hi : ∀ᵐ ω ∂μ, ∀ i j : Fin n, Integrable
      (fun r ↦ FiniteItoWeights.hessian Y G i j r ω * inner ℝ (R i (r, ω)) (R j (r, ω)))
      (timeMeasure H) := ae_all_iff.mpr (fun i ↦ ae_all_iff.mpr (fun j ↦
        (product_integrable (R i) (R j) (FiniteItoWeights.hessian Y G i j)
          (FiniteItoWeights.hessian_predictable Y hY hG i j) B (hb i j)).prod_left_ae))
  filter_upwards [hi] with ω hiω
  have he (r : ℝ≥0) : GaussianTaylorAverage.covarianceAction
      (fun i j ↦ inner ℝ (R i (r, ω)) (R j (r, ω)))
      (GaussianTaylor.hessian (G r) (Y (r, ω))) =
      ∑ i : Fin n, ∑ j : Fin n,
        FiniteItoWeights.hessian Y G i j r ω * inner ℝ (R i (r, ω)) (R j (r, ω)) := by
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    exact mul_comm _ _
  simp only [energy, he]
  rw [integral_finsetSum _ (fun i hi ↦ integrable_finsetSum _ (fun j hj ↦ hiω i j))]
  apply Finset.sum_congr rfl
  intro i hi
  rw [integral_finsetSum _ (fun j hj ↦ hiω i j)]
  rfl

/-- The full finite-dimensional quadratic term converges to the actual
covariance action of the original random Hilbert rows. -/
theorem tendstoInMeasure {ι : Type*} [Countable ι] [DecidableEq ι]
    (P : FiniteScalarIto.Family F μ H ι) (e : HilbertBasis ι ℝ C)
    (R : Fin n → Process (E := C) F μ H) (z : Ω → State n)
    (Y : ℝ≥0 × Ω → State n) (hY : StronglyMeasurable[F.predictable] Y)
    (hc : ∀ ω, Continuous (fun t ↦ Y (t, ω)))
    (hRep : ∀ t : ℝ≥0, t ≤ H → (fun ω ↦ Y (t, ω)) =ᵐ[μ]
      (fun ω ↦ StandardFiniteIto.vectorIntegral F μ H (FiniteCylindricalIto.terminalIto P.toCoordinates e) (z ω) R t ω))
    {a b : ℝ} {G dG : ℝ → State n → ℝ} (hG : RegularTest a b G dG) :
    TendstoInMeasure μ (sum (H := H) Y G) Filter.atTop (energy R Y G) := by
  let J := FiniteCylindricalIto.terminalIto P.toCoordinates e
  obtain ⟨B, hB, hb⟩ := FiniteItoWeights.hessian_bound Y hG
  have hlim (i j : Fin n) := NativeWeightedCovariation.tendstoInMeasure P e (R i) (R j)
    (FiniteItoWeights.hessian Y G i j) (FiniteItoWeights.hessian_adapted Y hY hG i j)
    (FiniteItoWeights.hessian_predictable Y hY hG i j)
    (Filter.Eventually.of_forall fun ω ↦ (FiniteItoWeights.hessian_continuous Y hG hc i j ω).continuousOn)
    B hB (hb i j)
  have hm (i j : Fin n) (m : ℕ) : AEStronglyMeasurable
      (NativeWeightedCovariation.sum J (R i) (R j) (FiniteItoWeights.hessian Y G i j) m) μ :=
    (measurable_mixed_sum J (R i) (R j) _ (FiniteItoWeights.hessian_adapted Y hY hG i j) m).aestronglyMeasurable
  have hsum := ConvergenceInMeasureAlgebra.finset_sum Finset.univ
    (fun i ↦ ConvergenceInMeasureAlgebra.finset_sum Finset.univ (hlim i) (hm i))
    (fun i m ↦ Finset.univ.aestronglyMeasurable_fun_sum (fun j hj ↦ hm i j m))
  exact TendstoInMeasure.congr (fun m ↦ (sum_ae J R z Y hRep G m).symm)
    (energy_sum_ae R Y hY hG).symm hsum

def normSum (Y : ℝ≥0 × Ω → State n) (m : ℕ) (ω : Ω) : ℝ :=
  ∑ k : Fin m, ‖Y (unifPart H m (k + 1), ω) - Y (unifPart H m k, ω)‖ ^ 2

theorem normSum_ae (J : StandardTerminalIto (C := C) (E := ℝ) F μ H)
    (R : Fin n → Process (E := C) F μ H) (z : Ω → State n) (Y : ℝ≥0 × Ω → State n)
    (hRep : ∀ t : ℝ≥0, t ≤ H → (fun ω ↦ Y (t, ω)) =ᵐ[μ]
      (fun ω ↦ StandardFiniteIto.vectorIntegral F μ H J (z ω) R t ω)) (m : ℕ) :
    normSum (H := H) Y m =ᵐ[μ] (fun ω ↦ ∑ i : Fin n,
      NativeWeightedQuadraticVariation.sum J (R i) (fun _ _ ↦ 1) m ω) := by
  filter_upwards [FiniteItoStochasticTerms.increment_rep J R z Y hRep m] with ω hω
  simp only [normSum, EuclideanSpace.real_norm_sq_eq]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro k hk
  rw [hω k i]
  exact (one_mul _).symm

/-- Total squared state increments have the genuine finite row-energy
limit. This supplies the pathwise boundedness needed for Taylor
remainders along a common almost-sure subsequence. -/
theorem normSum_tendstoInMeasure {ι : Type*} [Countable ι] [DecidableEq ι]
    (P : FiniteScalarIto.Family F μ H ι) (e : HilbertBasis ι ℝ C)
    (R : Fin n → Process (E := C) F μ H) (z : Ω → State n) (Y : ℝ≥0 × Ω → State n)
    (hRep : ∀ t : ℝ≥0, t ≤ H → (fun ω ↦ Y (t, ω)) =ᵐ[μ]
      (fun ω ↦ StandardFiniteIto.vectorIntegral F μ H (FiniteCylindricalIto.terminalIto P.toCoordinates e) (z ω) R t ω)) :
    TendstoInMeasure μ (normSum (H := H) Y) Filter.atTop
      (fun ω ↦ ∑ i : Fin n, NativeWeightedEnergy.integral (R i) (fun _ _ ↦ 1) ω) := by
  let J := FiniteCylindricalIto.terminalIto P.toCoordinates e
  have hw : StronglyAdapted F (fun _ _ ↦ (1 : ℝ)) := fun _ ↦ stronglyMeasurable_const
  have hp : StronglyMeasurable[F.predictable] (Function.uncurry (fun _ _ ↦ (1 : ℝ))) := stronglyMeasurable_const
  have hlim (i : Fin n) := NativeWeightedQuadraticVariation.tendstoInMeasure P e (R i) (fun _ _ ↦ 1)
    hw hp (Filter.Eventually.of_forall fun ω ↦ continuousOn_const) 1 zero_le_one (fun _ _ ↦ by norm_num)
  have hm (i : Fin n) (m : ℕ) : AEStronglyMeasurable
      (NativeWeightedQuadraticVariation.sum J (R i) (fun _ _ ↦ 1) m) μ :=
    (NativeWeightedQuadraticVariation.stronglyMeasurable_sum J (R i) _ hw m).aestronglyMeasurable
  exact TendstoInMeasure.congr_left (fun m ↦ (normSum_ae J R z Y hRep m).symm)
    (ConvergenceInMeasureAlgebra.finset_sum Finset.univ hlim hm)

end SHEStochastic.FiniteItoQuadraticTerms
