module

public import SHEStochastic.FiniteItoWeights
public import SHE.StandardFiniteIto

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
noncomputable section

namespace SHEStochastic.FiniteItoStochasticTerms
open MeasureTheory ProbabilityTheory SHE SHE.PredictableL2 SHE.StoppedItoInputs SHE.GaussianItoTest
open MathFin.QuadraticVariationL2
open scoped NNReal ENNReal Topology

variable {Ω C : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup C] [InnerProductSpace ℝ C] [CompleteSpace C]
  [MeasurableSpace C] [BorelSpace C] [SecondCountableTopology C]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {H : ℝ≥0} {n : ℕ}

theorem linear_apply (L : State n →L[ℝ] ℝ) (x : State n) :
    L x = ∑ i : Fin n, x i * L (EuclideanSpace.basisFun (Fin n) ℝ i) := by
  nth_rw 1 [← (EuclideanSpace.basisFun (Fin n) ℝ).sum_repr x]
  rw [map_sum]
  simp only [EuclideanSpace.basisFun_repr, map_smul, smul_eq_mul]

/-- At every finite partition, the continuous version has precisely
the increments of the supplied original scalar integrals. -/
theorem increment_rep (J : StandardTerminalIto (C := C) (E := ℝ) F μ H)
    (R : Fin n → Process (E := C) F μ H) (z : Ω → State n) (Y : ℝ≥0 × Ω → State n)
    (hRep : ∀ t : ℝ≥0, t ≤ H → (fun ω ↦ Y (t, ω)) =ᵐ[μ]
      (fun ω ↦ StandardFiniteIto.vectorIntegral F μ H J (z ω) R t ω)) (m : ℕ) :
    ∀ᵐ ω ∂μ, ∀ k : Fin m, ∀ i : Fin n,
      (Y (unifPart H m (k + 1), ω) - Y (unifPart H m k, ω)) i =
        J.integral (stop F μ H (unifPart H m (k + 1)) (R i)) ω -
          J.integral (stop F μ H (unifPart H m k) (R i)) ω := by
  filter_upwards [ae_all_iff.mpr (fun k : Fin m ↦ hRep (unifPart H m k)
      (MathFin.ItoIntegralBrownian.unifPart_le_T k.isLt.le)),
    ae_all_iff.mpr (fun k : Fin m ↦ hRep (unifPart H m (k + 1))
      (MathFin.ItoIntegralBrownian.unifPart_le_T (Nat.succ_le_of_lt k.isLt)))] with ω hl hr
  intro k i
  have hi := congrArg (fun x : State n ↦ x i) (hl k)
  have hj := congrArg (fun x : State n ↦ x i) (hr k)
  change Y (unifPart H m k, ω) i = z ω i + J.integral (stop F μ H (unifPart H m k) (R i)) ω at hi
  change Y (unifPart H m (k + 1), ω) i = z ω i + J.integral (stop F μ H (unifPart H m (k + 1)) (R i)) ω at hj
  change Y (unifPart H m (k + 1), ω) i - Y (unifPart H m k, ω) i = _
  rw [hi, hj]
  ring

def linearSum (Y : ℝ≥0 × Ω → State n) (G : ℝ → State n → ℝ) (m : ℕ) (ω : Ω) : ℝ :=
  ∑ k : Fin m, fderiv ℝ (G (unifPart H m k)) (Y (unifPart H m k, ω))
    (Y (unifPart H m (k + 1), ω) - Y (unifPart H m k, ω))

theorem linearSum_ae (J : StandardTerminalIto (C := C) (E := ℝ) F μ H)
    (R : Fin n → Process (E := C) F μ H) (z : Ω → State n) (Y : ℝ≥0 × Ω → State n)
    (hRep : ∀ t : ℝ≥0, t ≤ H → (fun ω ↦ Y (t, ω)) =ᵐ[μ]
      (fun ω ↦ StandardFiniteIto.vectorIntegral F μ H J (z ω) R t ω)) (G : ℝ → State n → ℝ) (m : ℕ) :
    linearSum (H := H) Y G m =ᵐ[μ] (fun ω ↦ ∑ i : Fin n,
      StochasticRiemannSums.sum J (R i) (FiniteItoWeights.gradient Y G i) m ω) := by
  filter_upwards [increment_rep J R z Y hRep m] with ω hω
  simp only [linearSum]
  have he : (∑ k : Fin m, fderiv ℝ (G (unifPart H m k)) (Y (unifPart H m k, ω))
      (Y (unifPart H m (k + 1), ω) - Y (unifPart H m k, ω))) =
      ∑ k : Fin m, ∑ i : Fin n,
        (Y (unifPart H m (k + 1), ω) - Y (unifPart H m k, ω)) i *
          fderiv ℝ (G (unifPart H m k)) (Y (unifPart H m k, ω))
            (EuclideanSpace.basisFun (Fin n) ℝ i) :=
    Finset.sum_congr rfl (fun k hk ↦ linear_apply _ _)
  rw [he, Finset.sum_comm]
  simp only [StochasticRiemannSums.sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro k hk
  rw [hω k i]
  dsimp [FiniteItoWeights.gradient, FiniteItoNoise.gradientCoefficient]
  ring

/-- The finite sum of canonical weighted inputs is exactly the existing
gradient-row input, not a newly postulated stochastic term. -/
theorem gradient_input_sum (R : Fin n → Process (E := C) F μ H)
    (Y : ℝ≥0 × Ω → State n) (hY : StronglyMeasurable[F.predictable] Y)
    {a b : ℝ} {G dG : ℝ → State n → ℝ} (hG : RegularTest a b G dG)
    (L : ℝ) (hL : ∀ i t ω, |FiniteItoWeights.gradient Y G i t ω| ≤ L) :
    (∑ i : Fin n, PredictableMultiplier.process (R i) (Function.uncurry (FiniteItoWeights.gradient Y G i))
      (FiniteItoWeights.gradient_predictable Y hY hG i) L (fun p ↦ hL i p.1 p.2)) =
        FiniteItoNoise.gradientProcess F μ H Y hY R G (FiniteItoNoise.regular_admissible hG) := by
  letI : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
  let U (i : Fin n) := PredictableMultiplier.process (R i)
    (Function.uncurry (FiniteItoWeights.gradient Y G i))
    (FiniteItoWeights.gradient_predictable Y hY hG i) L (fun p ↦ hL i p.1 p.2)
  apply PastItoAlgebra.eq_of_ambient_ae F μ H
  filter_upwards [ae_eq_of_ae_eq_trim (Lp.coeFn_finsetSum Finset.univ U),
    ae_all_iff.mpr (fun i : Fin n ↦ PredictableMultiplier.process_ae (R i) _ _ L (fun p ↦ hL i p.1 p.2)),
    FiniteItoNoise.gradientProcess_ae F μ H Y hY R G (FiniteItoNoise.regular_admissible hG)] with p hs hp hg
  rw [hs, hg]
  simp only [Finset.sum_apply, FiniteItoNoise.gradientRow]
  exact Finset.sum_congr rfl (fun i hi ↦ hp i)

/-- The complete finite-dimensional first-order term converges to the
original gradient-row integral, for arbitrary predictable random rows. -/
theorem linearSum_tendstoInMeasure (J : StandardTerminalIto (C := C) (E := ℝ) F μ H)
    (hlocal : StandardTerminalPastLocality J) (R : Fin n → Process (E := C) F μ H)
    (z : Ω → State n) (Y : ℝ≥0 × Ω → State n) (hY : StronglyMeasurable[F.predictable] Y)
    (hc : ∀ ω, Continuous (fun t ↦ Y (t, ω)))
    (hRep : ∀ t : ℝ≥0, t ≤ H → (fun ω ↦ Y (t, ω)) =ᵐ[μ]
      (fun ω ↦ StandardFiniteIto.vectorIntegral F μ H J (z ω) R t ω))
    {a b : ℝ} {G dG : ℝ → State n → ℝ} (hG : RegularTest a b G dG) :
    TendstoInMeasure μ (linearSum (H := H) Y G) Filter.atTop
      (J.integral (FiniteItoNoise.gradientProcess F μ H Y hY R G (FiniteItoNoise.regular_admissible hG))) := by
  obtain ⟨L, hL0, hL⟩ := FiniteItoWeights.gradient_bound Y hG
  let U (i : Fin n) := PredictableMultiplier.process (R i)
    (Function.uncurry (FiniteItoWeights.gradient Y G i))
    (FiniteItoWeights.gradient_predictable Y hY hG i) L (fun p ↦ hL i p.1 p.2)
  have hlim (i : Fin n) : TendstoInMeasure μ
      (StochasticRiemannSums.sum J (R i) (FiniteItoWeights.gradient Y G i)) Filter.atTop
      (J.integral (U i)) :=
    StochasticRiemannSums.tendstoInMeasure J hlocal (R i) (FiniteItoWeights.gradient Y G i)
      (FiniteItoWeights.gradient_adapted Y hY hG i) (FiniteItoWeights.gradient_predictable Y hY hG i)
      (Filter.Eventually.of_forall fun ω ↦ (FiniteItoWeights.gradient_continuous Y hG hc i ω).continuousOn)
      L hL0 (hL i)
  have hm (i : Fin n) (m : ℕ) :
      AEStronglyMeasurable (StochasticRiemannSums.sum J (R i) (FiniteItoWeights.gradient Y G i) m) μ :=
    (Lp.stronglyMeasurable _).aestronglyMeasurable.congr
      (StochasticRiemannSums.integral_input_ae J hlocal (R i) (FiniteItoWeights.gradient Y G i)
        (FiniteItoWeights.gradient_adapted Y hY hG i) L hL0 (hL i) m)
  have htot : (∑ i : Fin n, J.integral (U i)) =
      J.integral (FiniteItoNoise.gradientProcess F μ H Y hY R G (FiniteItoNoise.regular_admissible hG)) := by
    rw [← map_sum, gradient_input_sum R Y hY hG L hL]
  have hout : (fun ω ↦ ∑ i : Fin n, J.integral (U i) ω) =ᵐ[μ]
      J.integral (FiniteItoNoise.gradientProcess F μ H Y hY R G (FiniteItoNoise.regular_admissible hG)) := by
    have hs := Lp.coeFn_finsetSum Finset.univ (fun i : Fin n ↦ J.integral (U i))
    rw [htot] at hs
    filter_upwards [hs] with ω hω
    simpa only [Finset.sum_apply] using hω.symm
  exact TendstoInMeasure.congr (fun m ↦ (linearSum_ae J R z Y hRep G m).symm) hout
    (ConvergenceInMeasureAlgebra.finset_sum Finset.univ hlim hm)

end SHEStochastic.FiniteItoStochasticTerms
