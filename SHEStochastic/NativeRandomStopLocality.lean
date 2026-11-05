module

public import SHEStochastic.StoppedSquareZero
public import SHEStochastic.SquareCompensator
public import SHEStochastic.ContinuousBracket
public import SHE.StoppedDampingClock
public import SHEStochastic.ContinuousStoppedVersions

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
noncomputable section

namespace SHEStochastic.NativeRandomStopLocality
open MeasureTheory ProbabilityTheory SHE SHE.PredictableL2
open scoped NNReal

variable {Ω C : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup C] [InnerProductSpace ℝ C]
  [MeasurableSpace C] [BorelSpace C] [SecondCountableTopology C]
  (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ]
  (H : ℝ≥0)

/-- Vanishing of the actual predictable input before a random time
forces its pathwise energy to vanish there. No future event is pulled
inside an Ito integral in this argument. -/
theorem energy_zero (u : Process (E := C) F μ H) (τ : Ω → WithTop ℝ≥0)
    (hu : ∀ᵐ p ∂energyMeasure μ H, (p.1 : WithTop ℝ≥0) < τ p.2 → u p = 0) :
    ∀ᵐ ω ∂μ, ∀ q : ℝ≥0, stoppedProcess (PredictableBracket.energy u) τ q ω = 0 := by
  have hp := (Measure.measurePreserving_swap (μ := μ) (ν := timeMeasure H)).quasiMeasurePreserving.ae hu
  filter_upwards [Measure.ae_ae_of_ae_prod hp] with ω hω
  intro q
  apply integral_eq_zero_of_ae
  filter_upwards [hω] with s hs
  change (Set.Iio ((min (q : WithTop ℝ≥0) (τ ω)).untopA)).indicator
    (fun r ↦ ‖u (r, ω)‖ ^ 2) s = 0
  by_cases hsq : s < (min (q : WithTop ℝ≥0) (τ ω)).untopA
  · have hne : min (q : WithTop ℝ≥0) (τ ω) ≠ ⊤ :=
      ne_top_of_le_ne_top WithTop.coe_ne_top (min_le_left _ _)
    have hle : (s : WithTop ℝ≥0) < τ ω :=
      ((WithTop.lt_untopA_iff hne).mp hsq).trans_le (min_le_right _ _)
    rw [Set.indicator_of_mem (show s ∈ Set.Iio ((min (q : WithTop ℝ≥0) (τ ω)).untopA) from hsq)]
    have hz : u (s, ω) = 0 := hs hle
    rw [hz, norm_zero, zero_pow (by decide : 2 ≠ 0)]
  · exact Set.indicator_of_notMem
      (show s ∉ Set.Iio ((min (q : WithTop ℝ≥0) (τ ω)).untopA) from hsq) _

/-- Random-stop locality for the SAME continuous native integral. The
square compensator and the public optional-sampling proof discharge the
random-time step; deterministic terminal locality alone is insufficient. -/
theorem stopped_zero (J : StandardTerminalIto (C := C) (E := ℝ) F μ H)
    (hlocal : StandardTerminalPastLocality J)
    (hnull : NullCompleteFiltration.ContainsNullSets F μ)
    (u : Process (E := C) F μ H) (M : ℝ≥0 → Ω → ℝ)
    (hM : StronglyAdapted F M) (hc : ∀ᵐ ω ∂μ, Continuous (fun q ↦ M q ω))
    (hrep : ∀ q, M q =ᵐ[μ] (J.integral (StoppedItoInputs.stop F μ H q u) : Ω → ℝ))
    (τ : Ω → WithTop ℝ≥0) (hτ : IsStoppingTime F τ)
    (hu : ∀ᵐ p ∂energyMeasure μ H, (p.1 : WithTop ℝ≥0) < τ p.2 → u p = 0)
    (q : ℝ≥0) : ∀ᵐ ω ∂μ, stoppedProcess M τ q ω = 0 := by
  have hN := PredictableBracket.square_compensator_martingale J hlocal u hM hrep
  have hNc : ∀ᵐ ω ∂μ, Continuous (fun t ↦ M t ω ^ 2 - PredictableBracket.energy u t ω) := by
    filter_upwards [hc, PredictableBracket.continuous_monotone u] with ω hω he
    exact (hω.pow 2).sub he.1
  have hzero : ∀ᵐ ω ∂μ, M 0 ω ^ 2 - PredictableBracket.energy u 0 ω = 0 := by
    have h0 := hrep 0
    rw [NNReal.coe_zero, StoppedItoInputs.stop_zero, map_zero] at h0
    filter_upwards [h0, Lp.coeFn_zero ℝ 2 μ] with ω hω hz
    rw [hω, hz]
    simp [PredictableBracket.energy]
  exact StoppedSquareZero.stopped_zero μ F hnull M (PredictableBracket.energy u)
    hN hNc hzero τ hτ q ((energy_zero F μ H u τ hu).mono fun ω hω ↦ hω q)

/-- Inputs agreeing up to an exit give equal stopped continuous native
integrals. This is the form used to match a weak solution's convolution
with its bounded state localization. -/
theorem stopped_eq [CompleteSpace C] (J : StandardTerminalIto (C := C) (E := ℝ) F μ H)
    (hlocal : StandardTerminalPastLocality J)
    (hnull : NullCompleteFiltration.ContainsNullSets F μ)
    (u v : Process (E := C) F μ H) (M N : ℝ≥0 → Ω → ℝ)
    (hM : StronglyAdapted F M) (hN : StronglyAdapted F N)
    (hcM : ∀ᵐ ω ∂μ, Continuous (fun q ↦ M q ω))
    (hcN : ∀ᵐ ω ∂μ, Continuous (fun q ↦ N q ω))
    (hrepM : ∀ q, M q =ᵐ[μ] (J.integral (StoppedItoInputs.stop F μ H q u) : Ω → ℝ))
    (hrepN : ∀ q, N q =ᵐ[μ] (J.integral (StoppedItoInputs.stop F μ H q v) : Ω → ℝ))
    (τ : Ω → WithTop ℝ≥0) (hτ : IsStoppingTime F τ)
    (huv : ∀ᵐ p ∂energyMeasure μ H, (p.1 : WithTop ℝ≥0) < τ p.2 → u p = v p)
    (q : ℝ≥0) : ∀ᵐ ω ∂μ, stoppedProcess M τ q ω = stoppedProcess N τ q ω := by
  have hc : ∀ᵐ ω ∂μ, Continuous (fun q ↦ (M - N) q ω) := by
    filter_upwards [hcM, hcN] with ω hm hn
    exact hm.sub hn
  have hrep (t : ℝ≥0) : (M - N) t =ᵐ[μ]
      (J.integral (StoppedItoInputs.stop F μ H t (u - v)) : Ω → ℝ) := by
    rw [StoppedDampingClock.stop_sub, map_sub]
    filter_upwards [hrepM t, hrepN t,
      Lp.coeFn_sub (J.integral (StoppedItoInputs.stop F μ H t u))
        (J.integral (StoppedItoInputs.stop F μ H t v))] with ω hm hn hs
    change M t ω - N t ω = _
    rw [hs, Pi.sub_apply, hm, hn]
  have hz : ∀ᵐ p ∂energyMeasure μ H, (p.1 : WithTop ℝ≥0) < τ p.2 → (u - v) p = 0 := by
    filter_upwards [huv, ae_eq_of_ae_eq_trim (Lp.coeFn_sub u v)] with p hp hs hpt
    rw [hs, Pi.sub_apply, hp hpt, sub_self]
  exact (stopped_zero F μ H J hlocal hnull (u - v) (M - N)
    (hM.sub hN) hc hrep τ hτ hz q).mono fun ω hω ↦ sub_eq_zero.mp hω

/-- Terminal integrals of causal inputs agree on the event that the
observation time precedes the random exit. Their continuous versions
are supplied by the ordinary stopped-version package, and adaptation
is derived from the original native integral. -/
theorem integral_eq_before [CompleteSpace C]
    (J : StandardTerminalIto (C := C) (E := ℝ) F μ H)
    (hlocal : StandardTerminalPastLocality J) (hversions : ContinuousStoppedVersions J)
    (hnull : NullCompleteFiltration.ContainsNullSets F μ)
    (u v : Process (E := C) F μ H) (T : ℝ≥0)
    (huT : StoppedItoInputs.stop F μ H T u = u)
    (hvT : StoppedItoInputs.stop F μ H T v = v)
    (τ : Ω → WithTop ℝ≥0) (hτ : IsStoppingTime F τ)
    (huv : ∀ᵐ p ∂energyMeasure μ H, (p.1 : WithTop ℝ≥0) < τ p.2 → u p = v p) :
    ∀ᵐ ω ∂μ, (T : WithTop ℝ≥0) ≤ τ ω → J.integral u ω = J.integral v ω := by
  obtain ⟨M, hcM, hrepM⟩ := hversions u
  obtain ⟨N, hcN, hrepN⟩ := hversions v
  have ha (w : Process (E := C) F μ H) (Y : ℝ≥0 → Ω → ℝ)
      (hrep : ∀ q, Y q =ᵐ[μ] (J.integral (StoppedItoInputs.stop F μ H q w) : Ω → ℝ)) :
      StronglyAdapted F Y := by
    apply NullCompleteFiltration.stronglyAdapted_of_versions F μ hnull
    intro q
    obtain ⟨Z, hZ, he⟩ := StoppedItoInputs.stopped_integral_adapted F μ H J q w
    exact ⟨Z, hZ, (hrep q).trans he⟩
  have hh := stopped_eq F μ H J hlocal hnull u v M N
    (ha u M hrepM) (ha v N hrepN) (Filter.Eventually.of_forall hcM)
    (Filter.Eventually.of_forall hcN) hrepM hrepN τ hτ huv T
  have hm := hrepM T
  have hn := hrepN T
  rw [huT] at hm
  rw [hvT] at hn
  filter_upwards [hh, hm, hn] with ω hs hm hn hT
  rw [stoppedProcess_eq_of_le hT, stoppedProcess_eq_of_le hT] at hs
  exact hm.symm.trans (hs.trans hn)

end SHEStochastic.NativeRandomStopLocality
