module

public import SHE.StandardTerminalPastLocality
public import SHE.StandardTerminalNovikov
public import SHE.PastItoAlgebra
public import MathFin.Foundations.ItoIntegralL2

/-! Conditional second moments from the SAME integral's isometry and
proved past locality. The event-localization argument follows the public
PointwiseBracket.lean, formal-mathfin 3c41aee9bf2d9743f9e66b439f90d1635843d2d2;
it applies here to arbitrary Hilbert noise and the supplied filtration. -/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section

namespace SHEStochastic.ConditionalBracket
open MeasureTheory ProbabilityTheory SHE SHE.PredictableL2 SHE.PastItoInputs SHE.StoppedItoInputs
open scoped NNReal ENNReal
variable {Ω C : Type*} [MeasurableSpace Ω] [NormedAddCommGroup C] [InnerProductSpace ℝ C]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {μ : Measure Ω} [IsProbabilityMeasure μ] {H : ℝ≥0}

theorem second_moment (J : StandardTerminalIto (C := C) (E := ℝ) F μ H)
    (u : Process (E := C) F μ H) :
    (∫ ω, J.integral u ω ^ 2 ∂μ) = ∫ ω, StochasticExponential.bracket F μ H u ω ∂μ := by
  calc
    _ = ‖J.integral u‖ ^ 2 := (MathFin.ItoIntegralL2.lp_two_norm_sq _).symm
    _ = ‖u‖ ^ 2 := by rw [J.integral.norm_map]
    _ = _ := (StochasticExponential.expected_bracket F μ H u).symm

theorem event_bracket (a : ℝ≥0) (A : Set Ω) (hA : MeasurableSet[F a] A)
    (u : Process (E := C) F μ H) :
    StochasticExponential.bracket F μ H (eventProcess F μ H a A hA u) =ᵐ[μ]
      A.indicator (StochasticExponential.bracket F μ H (post F μ H a u)) := by
  have he := (Measure.measurePreserving_swap (μ := μ) (ν := timeMeasure H)).quasiMeasurePreserving.ae
    (eventProcess_ae F μ H a A hA u)
  have hp := (Measure.measurePreserving_swap (μ := μ) (ν := timeMeasure H)).quasiMeasurePreserving.ae
    (post_ae F μ H a u)
  filter_upwards [Measure.ae_ae_of_ae_prod he, Measure.ae_ae_of_ae_prod hp] with ω he hp
  by_cases hω : ω ∈ A
  · rw [Set.indicator_of_mem hω]
    apply integral_congr_ae
    filter_upwards [he, hp] with s hs ht
    dsimp only [Prod.swap] at hs ht
    rw [hs, ht]
    simp only [eventAfter, Set.indicator, Set.mem_prod, Set.mem_Ioi, hω, and_true]
  · rw [Set.indicator_of_notMem hω]
    change (∫ s, ‖eventProcess F μ H a A hA u (s, ω)‖ ^ 2 ∂timeMeasure H) = 0
    calc
      _ = ∫ _s : ℝ≥0, (0 : ℝ) ∂timeMeasure H := by
        apply integral_congr_ae
        filter_upwards [he] with s hs
        dsimp only [Prod.swap] at hs
        rw [hs, Set.indicator_of_notMem (show (s, ω) ∉ eventAfter a A from fun h ↦ hω h.2)]
        simp
      _ = _ := integral_zero _ _

theorem setIntegral_second (J : StandardTerminalIto (C := C) (E := ℝ) F μ H)
    (hlocal : StandardTerminalPastLocality J) (a : ℝ≥0)
    (A : Set Ω) (hA : MeasurableSet[F a] A) (u : Process (E := C) F μ H) :
    (∫ ω in A, J.integral (post F μ H a u) ω ^ 2 ∂μ) =
      ∫ ω in A, StochasticExponential.bracket F μ H (post F μ H a u) ω ∂μ := by
  have hL : (∫ ω, J.integral (eventProcess F μ H a A hA u) ω ^ 2 ∂μ) =
      ∫ ω in A, J.integral (post F μ H a u) ω ^ 2 ∂μ := by
    rw [← integral_indicator (F.le a A hA)]
    apply integral_congr_ae
    filter_upwards [hlocal a A hA u] with ω hω
    rw [hω]
    by_cases ha : ω ∈ A <;> simp [ha]
  have hR : (∫ ω, StochasticExponential.bracket F μ H (eventProcess F μ H a A hA u) ω ∂μ) =
      ∫ ω in A, StochasticExponential.bracket F μ H (post F μ H a u) ω ∂μ := by
    rw [← integral_indicator (F.le a A hA)]
    exact integral_congr_ae (event_bracket a A hA u)
  rw [← hL, second_moment, hR]

/-- Conditional bracket identity for arbitrary L2 inputs. This requires
neither an Ito formula nor a BDG estimate. -/
theorem condExp_second (J : StandardTerminalIto (C := C) (E := ℝ) F μ H)
    (hlocal : StandardTerminalPastLocality J) (a : ℝ≥0) (u : Process (E := C) F μ H) :
    μ[(fun ω ↦ J.integral (post F μ H a u) ω ^ 2) | F a] =ᵐ[μ]
      μ[StochasticExponential.bracket F μ H (post F μ H a u) | F a] := by
  refine (ae_eq_condExp_of_forall_setIntegral_eq (F.le a)
    (Lp.memLp (J.integral (post F μ H a u))).integrable_sq
    (fun s _ _ ↦ integrable_condExp.integrableOn) (fun s hs _ ↦ ?_)
    stronglyMeasurable_condExp.aestronglyMeasurable).symm
  rw [setIntegral_condExp (F.le a) (StochasticExponential.bracket_integrable F μ H _) hs]
  exact (setIntegral_second J hlocal a s hs u).symm

/-- Centering after localization implies zero conditional mean for every
future input, in the full supplied filtration. -/
theorem condExp_post_zero (J : StandardTerminalIto (C := C) (E := ℝ) F μ H)
    (hlocal : StandardTerminalPastLocality J) (a : ℝ≥0) (u : Process (E := C) F μ H) :
    μ[(J.integral (post F μ H a u) : Ω → ℝ) | F a] =ᵐ[μ] (fun _ ↦ (0 : ℝ)) := by
  refine (ae_eq_condExp_of_forall_setIntegral_eq (F.le a)
    ((Lp.memLp (J.integral (post F μ H a u))).integrable one_le_two)
    (fun _ _ _ ↦ (integrable_const (0 : ℝ)).integrableOn) (fun A hA _ ↦ ?_)
    stronglyMeasurable_zero.aestronglyMeasurable).symm
  change (∫ _ω in A, (0 : ℝ) ∂μ) = _
  rw [integral_zero, ← integral_indicator (F.le a A hA)]
  exact ((integral_congr_ae (hlocal a A hA u).symm).trans (J.centered _)).symm

variable [MeasurableSpace C] [BorelSpace C] [SecondCountableTopology C]

/-- The exact original stopped-input increment, with deterministic
endpoints identified in predictable L2. -/
theorem integral_increment (J : StandardTerminalIto (C := C) (E := ℝ) F μ H)
    {a b : ℝ≥0} (hab : a ≤ b) (u : Process (E := C) F μ H) :
    (J.integral (post F μ H a (stop F μ H b u)) : Ω → ℝ) =ᵐ[μ]
      fun ω ↦ J.integral (stop F μ H b u) ω - J.integral (stop F μ H a u) ω := by
  rw [PastItoAlgebra.post_stop_eq_sub F μ H a b hab, map_sub]
  exact Lp.coeFn_sub _ _

/-- Conditional isometry for an increment of the actual integral; the
bracket is the actual pathwise energy on that same time band. -/
theorem condExp_increment_second (J : StandardTerminalIto (C := C) (E := ℝ) F μ H)
    (hlocal : StandardTerminalPastLocality J) {a b : ℝ≥0} (hab : a ≤ b)
    (u : Process (E := C) F μ H) :
    μ[(fun ω ↦ (J.integral (stop F μ H b u) ω - J.integral (stop F μ H a u) ω) ^ 2) | F a]
      =ᵐ[μ] μ[StochasticExponential.bracket F μ H (post F μ H a (stop F μ H b u)) | F a] := by
  exact (condExp_congr_ae ((integral_increment J hab u).pow_const 2).symm).trans
    (condExp_second J hlocal a _)

/-- Every stopped integral has the martingale conditional-mean identity.
Only isometry, centering, adaptedness and proved past locality are used. -/
theorem condExp_stopped (J : StandardTerminalIto (C := C) (E := ℝ) F μ H)
    (hlocal : StandardTerminalPastLocality J) {a b : ℝ≥0} (hab : a ≤ b)
    (u : Process (E := C) F μ H) :
    μ[(J.integral (stop F μ H b u) : Ω → ℝ) | F a] =ᵐ[μ]
      (J.integral (stop F μ H a u) : Ω → ℝ) := by
  have ha := (Lp.memLp (J.integral (stop F μ H a u))).integrable one_le_two
  have hb := (Lp.memLp (J.integral (stop F μ H b u))).integrable one_le_two
  obtain ⟨Z, hZ, hrep⟩ := stopped_integral_adapted F μ H J a u
  have hae : AEStronglyMeasurable[F a] (J.integral (stop F μ H a u) : Ω → ℝ) μ :=
    hZ.aestronglyMeasurable.congr hrep.symm
  have he := (condExp_congr_ae (integral_increment J hab u).symm).trans
    (condExp_post_zero J hlocal a (stop F μ H b u))
  filter_upwards [he, condExp_sub hb ha (F a),
    condExp_of_aestronglyMeasurable' (F.le a) hae ha] with ω he hs ha
  change (μ[(J.integral (stop F μ H b u) : Ω → ℝ) -
    (J.integral (stop F μ H a u) : Ω → ℝ) | F a]) ω = 0 at he
  simp only [Pi.sub_apply] at hs
  rw [hs, ha] at he
  linarith

/-- Any adapted representatives of the same stopped integrals form a
martingale. This separates representative bookkeeping from stochastic
construction and applies to scalar integrals with any Hilbert noise. -/
theorem martingale (J : StandardTerminalIto (C := C) (E := ℝ) F μ H)
    (hlocal : StandardTerminalPastLocality J) (u : Process (E := C) F μ H)
    {M : ℝ≥0 → Ω → ℝ} (hm : StronglyAdapted F M)
    (hrep : ∀ t, M t =ᵐ[μ] (J.integral (stop F μ H t u) : Ω → ℝ)) :
    Martingale M F μ := by
  refine ⟨hm, fun a b hab ↦ ?_⟩
  exact (condExp_congr_ae (hrep b)).trans
    ((condExp_stopped J hlocal hab u).trans (hrep a).symm)

end SHEStochastic.ConditionalBracket
