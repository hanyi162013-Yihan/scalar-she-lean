module

public import SHEStochastic.SquareCompensator
public import SHE.StoppedDampingClock

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 700000
noncomputable section

namespace SHEStochastic.NativeCrossCompensator
open MeasureTheory ProbabilityTheory SHE SHE.PredictableL2
open scoped NNReal ENNReal

variable {Ω C : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup C] [InnerProductSpace ℝ C] [CompleteSpace C]
  [MeasurableSpace C] [BorelSpace C] [SecondCountableTopology C]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {μ : Measure Ω} [IsProbabilityMeasure μ] {H : ℝ≥0}

/-- Polarization of the actual predictable energies. -/
def value (u v : Process (E := C) F μ H) (t : ℝ≥0) (sample : Ω) : ℝ :=
  (PredictableBracket.energy u t sample + PredictableBracket.energy v t sample -
    PredictableBracket.energy (u-v) t sample) / 2

/-- Polarization is the literal time integral of the cross inner
product, simultaneously at every deterministic endpoint. -/
theorem value_ae (u v : Process (E := C) F μ H) :
    ∀ᵐ sample ∂μ, ∀ t : ℝ≥0, value u v t sample =
      ∫ s, (Set.Iio t).indicator (fun s ↦ inner ℝ (u (s,sample)) (v (s,sample))) s ∂timeMeasure H := by
  have hu := (memLp_of_memLp_trim (predictable_le_product F) (Lp.memLp u)).norm.integrable_sq
  have hv := (memLp_of_memLp_trim (predictable_le_product F) (Lp.memLp v)).norm.integrable_sq
  have hw := (memLp_of_memLp_trim (predictable_le_product F) (Lp.memLp (u-v))).norm.integrable_sq
  have hs := (Measure.measurePreserving_swap (μ := μ) (ν := timeMeasure H)).quasiMeasurePreserving.ae
    (ae_eq_of_ae_eq_trim (Lp.coeFn_sub u v))
  filter_upwards [hu.prod_left_ae, hv.prod_left_ae, hw.prod_left_ae, Measure.ae_ae_of_ae_prod hs]
    with sample hu hv hw hs
  intro t
  let U := (Set.Iio t).indicator (fun s ↦ ‖u (s,sample)‖^2)
  let V := (Set.Iio t).indicator (fun s ↦ ‖v (s,sample)‖^2)
  let W := (Set.Iio t).indicator (fun s ↦ ‖(u-v) (s,sample)‖^2)
  have hU : Integrable U (timeMeasure H) := hu.indicator measurableSet_Iio
  have hV : Integrable V (timeMeasure H) := hv.indicator measurableSet_Iio
  have hW : Integrable W (timeMeasure H) := hw.indicator measurableSet_Iio
  change ((∫ s, U s ∂timeMeasure H) + (∫ s, V s ∂timeMeasure H) - (∫ s, W s ∂timeMeasure H)) / 2 = _
  have hLin := (integral_sub (hU.add hV) hW).trans
    (congrArg (fun z : ℝ ↦ z-∫ s, W s ∂timeMeasure H) (integral_add hU hV))
  have hInt := (integral_div (μ := timeMeasure H) (2 : ℝ) (U+V-W)).trans
    (congrArg (fun z : ℝ ↦ z/2) hLin)
  rw [← hInt]
  apply integral_congr_ae
  filter_upwards [hs] with s hs
  dsimp only [Prod.swap] at hs
  simp only [Pi.add_apply, Pi.sub_apply]
  by_cases ht : s < t
  · simp only [U, V, W, Set.indicator_apply, Set.mem_Iio, ht, ite_true]
    rw [hs]
    simp only [Pi.sub_apply]
    nlinarith [norm_sub_sq_real (u (s,sample)) (v (s,sample))]
  · simp only [U, V, W, Set.indicator_apply, Set.mem_Iio, ht, ite_false, zero_add, sub_self, zero_div]

/-- The cross compensator of two SAME-integral versions follows from
the existing square-compensator theorem by polarization. -/
theorem martingale (J : StandardTerminalIto (C := C) (E := ℝ) F μ H)
    (hlocal : StandardTerminalPastLocality J) (u v : Process (E := C) F μ H)
    (M N : ℝ≥0 → Ω → ℝ) (hM : StronglyAdapted F M) (hN : StronglyAdapted F N)
    (hRepM : ∀ t, M t =ᵐ[μ] (J.integral (StoppedItoInputs.stop F μ H t u) : Ω → ℝ))
    (hRepN : ∀ t, N t =ᵐ[μ] (J.integral (StoppedItoInputs.stop F μ H t v) : Ω → ℝ)) :
    Martingale (fun t sample ↦ M t sample * N t sample - value u v t sample) F μ := by
  have hr (t : ℝ≥0) : (M-N) t =ᵐ[μ]
      (J.integral (StoppedItoInputs.stop F μ H t (u-v)) : Ω → ℝ) := by
    rw [StoppedDampingClock.stop_sub, map_sub]
    exact ((hRepM t).sub (hRepN t)).trans (Lp.coeFn_sub _ _).symm
  have hm := PredictableBracket.square_compensator_martingale J hlocal u hM hRepM
  have hn := PredictableBracket.square_compensator_martingale J hlocal v hN hRepN
  have hd := PredictableBracket.square_compensator_martingale J hlocal (u-v) (hM.sub hN) hr
  convert ((hm.add hn).sub hd).smul (1/2 : ℝ) using 1
  funext t sample
  simp only [Pi.smul_apply, Pi.add_apply, Pi.sub_apply, smul_eq_mul, value]
  ring

end SHEStochastic.NativeCrossCompensator
