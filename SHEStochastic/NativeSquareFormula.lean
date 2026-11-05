module

public import SHEStochastic.UnboundedStochasticRiemannSums
public import SHEStochastic.NativeWeightedQuadraticVariation

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
noncomputable section

namespace SHEStochastic.NativeSquareFormula
open MeasureTheory ProbabilityTheory SHE SHE.PredictableL2 Filter
open MathFin.QuadraticVariationL2
open scoped NNReal ENNReal Topology

theorem discrete (H : ℝ≥0) (x : ℝ≥0 → ℝ) (m : ℕ) (hm : 0 < m) :
    x H ^ 2 - x 0 ^ 2 =
      2 * (∑ i : Fin m, x (unifPart H m i) * (x (unifPart H m (i + 1)) - x (unifPart H m i))) +
        ∑ i : Fin m, (x (unifPart H m (i + 1)) - x (unifPart H m i)) ^ 2 := by
  have ht : (∑ i : Fin m, (x (unifPart H m (i + 1)) ^ 2 - x (unifPart H m i) ^ 2)) =
      x H ^ 2 - x 0 ^ 2 := by
    rw [Fin.sum_univ_eq_sum_range (fun k : ℕ ↦ x (unifPart H m (k + 1)) ^ 2 - x (unifPart H m k) ^ 2),
      Finset.sum_range_sub (fun k ↦ x (unifPart H m k) ^ 2)]
    have hm0 : (m : ℝ≥0) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
    simp [unifPart, hm0]
  rw [← ht, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun i _ ↦ by ring)

variable {Ω C ι : Type*} [MeasurableSpace Ω] [Countable ι] [DecidableEq ι]
  [NormedAddCommGroup C] [InnerProductSpace ℝ C] [CompleteSpace C]
  [MeasurableSpace C] [BorelSpace C] [SecondCountableTopology C]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {H : ℝ≥0}

/-- The unbounded quadratic test has an actual stochastic integral,
not merely a compensated-square martingale. A random L² path envelope
replaces a deterministic bound on the derivative of the test. -/
theorem formula (P : FiniteScalarIto.Family F μ H ι) (e : HilbertBasis ι ℝ C)
    (u : Process (E := C) F μ H) (M : ℝ) (hM : 0 ≤ M)
    (hu : ∀ᵐ p ∂(energyMeasure μ H).trim (predictable_le_product F), ‖u p‖ ≤ M)
    (Y : ℝ≥0 → Ω → ℝ) (hY : StronglyAdapted F Y)
    (hp : StronglyMeasurable[F.predictable] (Function.uncurry Y))
    (hc : ∀ᵐ ω ∂μ, ContinuousOn (fun t ↦ Y t ω) (Set.Icc 0 H))
    (hRep : ∀ t : ℝ≥0, Y t =ᵐ[μ]
      (FiniteCylindricalIto.terminalIto P.toCoordinates e).integral (StoppedItoInputs.stop F μ H t u))
    (D : Ω → ℝ) (hD : MemLp D 2 μ) (hD0 : ∀ ω, 0 ≤ D ω)
    (hb : ∀ᵐ ω ∂μ, ∀ t, |Y t ω| ≤ D ω) :
    ∀ᵐ ω ∂μ, Y H ω ^ 2 - Y 0 ω ^ 2 =
      2 * (FiniteCylindricalIto.terminalIto P.toCoordinates e).integral
        (PredictableEnvelopeMultiplier.process u M hM hu (Function.uncurry Y) hp D hD
          (PredictableEnvelopeMultiplier.path_bound Y D hb)) ω + ∫ r, ‖u (r, ω)‖ ^ 2 ∂timeMeasure H := by
  let J := FiniteCylindricalIto.terminalIto P.toCoordinates e
  have hS := UnboundedStochasticRiemannSums.tendstoInMeasure J
    (FiniteCylindricalIto.pastLocality P e) u M hM hu Y hY hp hc D hD hD0 hb
  have hQ := NativeWeightedQuadraticVariation.tendstoInMeasure P e u (fun _ _ ↦ 1)
    (fun _ ↦ stronglyMeasurable_const) stronglyMeasurable_const
    (Eventually.of_forall fun _ ↦ continuousOn_const) 1 (by norm_num) (fun _ _ ↦ by norm_num)
  have hgrid : ∀ᵐ ω ∂μ, ∀ m j : ℕ, Y (unifPart H m j) ω =
      J.integral (StoppedItoInputs.stop F μ H (unifPart H m j) u) ω :=
    ae_all_iff.mpr (fun m ↦ ae_all_iff.mpr (fun j ↦ hRep (unifPart H m j)))
  obtain ⟨ns, hns, hs, hq⟩ := MathFin.exists_subseq_tendsto_ae₂ hS hQ id Filter.tendsto_id
  filter_upwards [hs, hq, hgrid] with ω hsω hqω hg
  have ht := (hsω.const_mul 2).add hqω
  have he : (fun k ↦ 2 * StochasticRiemannSums.sum J u Y (ns k) ω +
      NativeWeightedQuadraticVariation.sum J u (fun _ _ ↦ 1) (ns k) ω) =ᶠ[atTop]
        (fun _ ↦ Y H ω ^ 2 - Y 0 ω ^ 2) := by
    filter_upwards [hns.tendsto_atTop.eventually (eventually_gt_atTop 0)] with k hk
    rw [discrete H (fun r ↦ Y r ω) (ns k) hk]
    simp only [StochasticRiemannSums.sum, NativeWeightedQuadraticVariation.sum, one_mul]
    congr 1
    · apply congrArg (fun x : ℝ ↦ 2 * x)
      apply Finset.sum_congr rfl
      intro i hi
      rw [← hg (ns k) (i + 1), ← hg (ns k) i]
    · apply Finset.sum_congr rfl
      intro i hi
      rw [← hg (ns k) (i + 1), ← hg (ns k) i]
  have hh := tendsto_nhds_unique (tendsto_const_nhds (x := Y H ω ^ 2 - Y 0 ω ^ 2)) (ht.congr' he)
  simpa only [NativeWeightedEnergy.integral, one_mul] using hh

end SHEStochastic.NativeSquareFormula
