module

public import SHEStochastic.StochasticRiemannSums
public import SHEStochastic.PredictableEnvelopeMultiplier
public import SHEStochastic.UnboundedPastMultiplier

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
noncomputable section

namespace SHEStochastic.UnboundedStochasticRiemannSums
open MeasureTheory ProbabilityTheory SHE SHE.PredictableL2 Filter
open MathFin.QuadraticVariationL2
open scoped NNReal ENNReal Topology

variable {Ω C : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup C] [InnerProductSpace ℝ C] [CompleteSpace C]
  [MeasurableSpace C] [BorelSpace C] [SecondCountableTopology C]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {H : ℝ≥0}

theorem step_bound (w : ℝ≥0 → Ω → ℝ) (D : Ω → ℝ) (hD0 : ∀ ω, 0 ≤ D ω)
    (hb : ∀ᵐ ω ∂μ, ∀ t, |w t ω| ≤ D ω) (n : ℕ) :
    ∀ᵐ p ∂energyMeasure μ H, |PredictableLeftSteps.step (H := H) w n p| ≤ D p.2 := by
  filter_upwards [(Measure.quasiMeasurePreserving_snd (μ := timeMeasure H) (ν := μ)).ae hb]
    with p hp
  exact PredictableLeftSteps.bound (fun t (_ : Ω) ↦ w t p.2) (D p.2) (hD0 p.2)
    (fun t _ ↦ hp t) n p

def input (u : Process (E := C) F μ H) (M : ℝ) (hM : 0 ≤ M)
    (hu : ∀ᵐ p ∂(energyMeasure μ H).trim (predictable_le_product F), ‖u p‖ ≤ M)
    (w : ℝ≥0 → Ω → ℝ) (hw : StronglyAdapted F w)
    (D : Ω → ℝ) (hD : MemLp D 2 μ) (hD0 : ∀ ω, 0 ≤ D ω)
    (hb : ∀ᵐ ω ∂μ, ∀ t, |w t ω| ≤ D ω) (n : ℕ) : Process (E := C) F μ H :=
  PredictableEnvelopeMultiplier.process u M hM hu (PredictableLeftSteps.step (H := H) w n)
    (PredictableLeftSteps.predictable w hw n) D hD (step_bound w D hD0 hb n)

theorem integral_input_ae (J : StandardTerminalIto (C := C) (E := ℝ) F μ H)
    (hlocal : StandardTerminalPastLocality J) (u : Process (E := C) F μ H)
    (M : ℝ) (hM : 0 ≤ M)
    (hu : ∀ᵐ p ∂(energyMeasure μ H).trim (predictable_le_product F), ‖u p‖ ≤ M)
    (w : ℝ≥0 → Ω → ℝ) (hw : StronglyAdapted F w)
    (D : Ω → ℝ) (hD : MemLp D 2 μ) (hD0 : ∀ ω, 0 ≤ D ω)
    (hb : ∀ᵐ ω ∂μ, ∀ t, |w t ω| ≤ D ω) (n : ℕ) :
    J.integral (input u M hM hu w hw D hD hD0 hb n) =ᵐ[μ]
      StochasticRiemannSums.sum J u w n := by
  classical
  let W (i : Fin n) := PredictableSteps.step (unifPart H n i) (unifPart H n (i + 1))
    (w (unifPart H n i))
  have hWp (i : Fin n) : StronglyMeasurable[F.predictable] (W i) :=
    PredictableSteps.step_stronglyMeasurable F _ _ (hw _)
  have hWb (i : Fin n) : ∀ᵐ p ∂energyMeasure μ H, |W i p| ≤ D p.2 := by
    filter_upwards [(Measure.quasiMeasurePreserving_snd (μ := timeMeasure H) (ν := μ)).ae hb]
      with p hp
    dsimp [W, PredictableSteps.step]
    split_ifs
    · exact hp _
    · simpa only [abs_zero] using hD0 p.2
  let V (i : Fin n) := PredictableEnvelopeMultiplier.process u M hM hu (W i) (hWp i) D hD (hWb i)
  have hV (i : Fin n) : V i =ᵐ[energyMeasure μ H] (fun p ↦ W i p • u p) :=
    PredictableEnvelopeMultiplier.process_ae u M hM hu (W i) (hWp i) D hD (hWb i)
  have hJ (i : Fin n) := UnboundedPastMultiplier.cell J hlocal u (V i)
    (unifPart H n i) (unifPart H n (i + 1))
    (MathFin.ItoIntegralBrownian.unifPart_mono H n (Nat.le_succ _))
    (w (unifPart H n i)) (hw _) (hV i)
  letI : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
  have hs : (∑ i, V i) = input u M hM hu w hw D hD hD0 hb n := by
    apply PastItoAlgebra.eq_of_ambient_ae F μ H
    filter_upwards [ae_eq_of_ae_eq_trim (Lp.coeFn_finsetSum Finset.univ V),
      ae_all_iff.mpr hV,
      PredictableEnvelopeMultiplier.process_ae u M hM hu _
        (PredictableLeftSteps.predictable w hw n) D hD (step_bound w D hD0 hb n)] with p hs hp hq
    change input u M hM hu w hw D hD hD0 hb n p = _ at hq
    rw [hs, hq]
    simp only [Finset.sum_apply]
    calc
      _ = ∑ i : Fin n, W i p • u p := Finset.sum_congr rfl (fun i _ ↦ hp i)
      _ = (∑ i : Fin n, W i p) • u p := Finset.sum_smul.symm
      _ = _ := by
        rw [Fin.sum_univ_eq_sum_range (fun k : ℕ ↦ PredictableSteps.step
          (unifPart H n k) (unifPart H n (k + 1)) (w (unifPart H n k)) p)]
        simp only [PredictableLeftSteps.step, WeightedPrimitiveSums.step,
          PredictableSteps.step, Set.indicator_apply]
  rw [← hs, map_sum]
  filter_upwards [Lp.coeFn_finsetSum Finset.univ (fun i ↦ J.integral (V i)), ae_all_iff.mpr hJ]
    with ω hs hω
  rw [hs]
  simp only [Finset.sum_apply]
  exact Finset.sum_congr rfl (fun i _ ↦ hω i)

/-- A continuous adapted stochastic multiplier with a random L² path
envelope is allowed; no deterministic bound on the multiplier is needed. -/
theorem tendstoInMeasure (J : StandardTerminalIto (C := C) (E := ℝ) F μ H)
    (hlocal : StandardTerminalPastLocality J) (u : Process (E := C) F μ H)
    (M : ℝ) (hM : 0 ≤ M)
    (hu : ∀ᵐ p ∂(energyMeasure μ H).trim (predictable_le_product F), ‖u p‖ ≤ M)
    (w : ℝ≥0 → Ω → ℝ) (hw : StronglyAdapted F w)
    (hp : StronglyMeasurable[F.predictable] (Function.uncurry w))
    (hc : ∀ᵐ ω ∂μ, ContinuousOn (fun t ↦ w t ω) (Set.Icc 0 H))
    (D : Ω → ℝ) (hD : MemLp D 2 μ) (hD0 : ∀ ω, 0 ≤ D ω)
    (hb : ∀ᵐ ω ∂μ, ∀ t, |w t ω| ≤ D ω) :
    TendstoInMeasure μ (StochasticRiemannSums.sum J u w) atTop
      (J.integral (PredictableEnvelopeMultiplier.process u M hM hu (Function.uncurry w) hp D hD
        (PredictableEnvelopeMultiplier.path_bound w D hb))) := by
  have ht := PredictableEnvelopeMultiplier.tendsto u M hM hu
    (fun n ↦ PredictableLeftSteps.step (H := H) w n)
    (fun n ↦ PredictableLeftSteps.predictable w hw n) (Function.uncurry w) hp D hD
    (step_bound w D hD0 hb) (PredictableEnvelopeMultiplier.path_bound w D hb)
    (ae_of_ae_trim (predictable_le_product F) (PredictableLeftSteps.tendsto_ae_trim w hw hp hc))
  have hi := tendstoInMeasure_of_tendsto_Lp (J.integral.continuous.tendsto _ |>.comp ht)
  exact TendstoInMeasure.congr_left (fun n ↦ integral_input_ae J hlocal u M hM hu w hw D hD hD0 hb n) hi

end SHEStochastic.UnboundedStochasticRiemannSums
