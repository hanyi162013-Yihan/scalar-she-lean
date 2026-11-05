module

public import SHEStochastic.PredictableLeftSteps

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
noncomputable section

namespace SHEStochastic.StochasticRiemannSums
open MeasureTheory ProbabilityTheory SHE SHE.PredictableL2 SHE.StoppedItoInputs
open MathFin.QuadraticVariationL2
open scoped NNReal ENNReal Topology

variable {Ω C : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup C] [InnerProductSpace ℝ C] [CompleteSpace C]
  [MeasurableSpace C] [BorelSpace C] [SecondCountableTopology C]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {H : ℝ≥0}

def sum (J : StandardTerminalIto (C := C) (E := ℝ) F μ H)
    (u : Process (E := C) F μ H) (w : ℝ≥0 → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  ∑ i : Fin n, w (unifPart H n i) ω *
    (J.integral (stop F μ H (unifPart H n (i + 1)) u) ω -
      J.integral (stop F μ H (unifPart H n i) u) ω)

/-- Sum the already proved cell rule; no new construction of the
stochastic integral is introduced. -/
theorem exists_input (J : StandardTerminalIto (C := C) (E := ℝ) F μ H)
    (hlocal : StandardTerminalPastLocality J) (u : Process (E := C) F μ H)
    (w : ℝ≥0 → Ω → ℝ) (hw : StronglyAdapted F w)
    (B : ℝ) (hB : 0 ≤ B) (hwb : ∀ t ω, |w t ω| ≤ B) (n : ℕ) :
    ∃ v : Process (E := C) F μ H,
      v =ᵐ[energyMeasure μ H] (fun p ↦ PredictableLeftSteps.step (H := H) w n p • u p) ∧
      J.integral v =ᵐ[μ] sum J u w n := by
  classical
  letI : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
  have hcell (i : Fin n) := PredictableMultiplier.cell J hlocal u
    (unifPart H n i) (unifPart H n (i + 1))
    (MathFin.ItoIntegralBrownian.unifPart_mono H n (Nat.le_succ _))
    (w (unifPart H n i)) (hw _) B hB (hwb _)
  choose V hv hJ using hcell
  refine ⟨∑ i, V i, ?_, ?_⟩
  · filter_upwards [ae_eq_of_ae_eq_trim (Lp.coeFn_finsetSum Finset.univ V), ae_all_iff.mpr hv]
      with p hs hp
    rw [hs]
    simp only [Finset.sum_apply]
    calc
      _ = ∑ i : Fin n, PredictableSteps.step (unifPart H n i) (unifPart H n (i + 1))
          (w (unifPart H n i)) p • u p := Finset.sum_congr rfl (fun i _ ↦ hp i)
      _ = (∑ i : Fin n, PredictableSteps.step (unifPart H n i) (unifPart H n (i + 1))
          (w (unifPart H n i)) p) • u p := Finset.sum_smul.symm
      _ = _ := by
        rw [Fin.sum_univ_eq_sum_range (fun i : ℕ ↦ PredictableSteps.step
          (unifPart H n i) (unifPart H n (i + 1)) (w (unifPart H n i)) p)]
        simp only [PredictableLeftSteps.step, WeightedPrimitiveSums.step,
          PredictableSteps.step, Set.indicator_apply]
  · rw [map_sum]
    filter_upwards [Lp.coeFn_finsetSum Finset.univ (fun i ↦ J.integral (V i)), ae_all_iff.mpr hJ]
      with ω hs hω
    rw [hs]
    simp only [Finset.sum_apply]
    exact Finset.sum_congr rfl (fun i _ ↦ hω i)

theorem integral_input_ae (J : StandardTerminalIto (C := C) (E := ℝ) F μ H)
    (hlocal : StandardTerminalPastLocality J) (u : Process (E := C) F μ H)
    (w : ℝ≥0 → Ω → ℝ) (hw : StronglyAdapted F w)
    (B : ℝ) (hB : 0 ≤ B) (hwb : ∀ t ω, |w t ω| ≤ B) (n : ℕ) :
    J.integral (PredictableLeftSteps.input u w hw B hB hwb n) =ᵐ[μ] sum J u w n := by
  obtain ⟨v, hv, hJ⟩ := exists_input J hlocal u w hw B hB hwb n
  have he : v = PredictableLeftSteps.input u w hw B hB hwb n :=
    PastItoAlgebra.eq_of_ambient_ae F μ H
      (hv.trans (PredictableMultiplier.process_ae u _ _ B _).symm)
  rwa [he] at hJ

/-- Left stochastic sums converge to the SAME terminal integral of the
weighted row, for arbitrary predictable L² inputs and continuous weights. -/
theorem tendstoInMeasure (J : StandardTerminalIto (C := C) (E := ℝ) F μ H)
    (hlocal : StandardTerminalPastLocality J) (u : Process (E := C) F μ H)
    (w : ℝ≥0 → Ω → ℝ) (hw : StronglyAdapted F w)
    (hp : StronglyMeasurable[F.predictable] (Function.uncurry w))
    (hc : ∀ᵐ ω ∂μ, ContinuousOn (fun t ↦ w t ω) (Set.Icc 0 H))
    (B : ℝ) (hB : 0 ≤ B) (hwb : ∀ t ω, |w t ω| ≤ B) :
    TendstoInMeasure μ (sum J u w) Filter.atTop
      (J.integral (PredictableMultiplier.process u (Function.uncurry w) hp B (fun p ↦ hwb p.1 p.2))) := by
  have ht := tendstoInMeasure_of_tendsto_Lp
    (J.integral.continuous.tendsto _ |>.comp
      (PredictableLeftSteps.tendsto_input u w hw hp hc B hB hwb))
  exact TendstoInMeasure.congr_left (fun n ↦ integral_input_ae J hlocal u w hw B hB hwb n) ht

end SHEStochastic.StochasticRiemannSums
