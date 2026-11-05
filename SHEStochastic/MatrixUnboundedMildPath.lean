module

public import SHEStochastic.MatrixUnboundedMildBeforeExit
public import SHEStochastic.ContinuousEqualityBeforeExit

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1100000
noncomputable section

namespace SHEStochastic.MatrixUnboundedMildPath
open MeasureTheory SHE MatrixInfiniteHaar HeatParameterCover
open StoppedPathPasting AdaptedCanonicalPathTests
open scoped NNReal ENNReal Matrix.Norms.L2Operator
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance : Fact (0 < 2*Real.pi) := ⟨by positivity⟩
local instance : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by simp⟩
variable {n : ℕ}
local instance : SecondCountableTopology (Physical (d := Fin n)) := Lp.SecondCountableTopology
local instance : MeasurableSpace (Physical (d := Fin n)) := borel _
local instance : BorelSpace (Physical (d := Fin n)) := ⟨rfl⟩
variable {G : EuclideanSpace ℝ (Fin n) → Matrix (Fin n) (Fin n) ℝ} {C β : ℝ≥0}
    {hG : HolderWith C β G} {hβ : 0<β} {hβ1 : β<1}
    {ρ₀ : MatrixLocalBlockChain.L2Law (n := n)}
    (S : MatrixUnboundedGlobalWeakExistence.Solution G hG hβ hβ1 ρ₀)

local notation "ρ" => (Measure.dirac () : Measure Unit)
local notation "μc" => IndependentNoiseCompletion.measure ρ S.law.toMeasure
local instance (priority := 2000) completedSigma :
    MeasurableSpace (RandomInitialBrownianFamily.Space ρ S.law.toMeasure) :=
  MatrixUnboundedCompletedGlobal.completedSigma S

theorem continuous_clock (H : ℝ≥0) : Continuous (toNN H) :=
  (continuous_subtype_val : Continuous (fun t : Time H => t.val)).subtype_mk _

/-- The assembled stochastic convolution is continuous through every
physical time of a chosen finite horizon. -/
theorem convolution_continuous (H : ℝ≥0) (hH : 0<H)
    (ω : RandomInitialBrownianFamily.Space ρ S.law.toMeasure) :
    Continuous (fun t : Time H =>
      MatrixUnboundedContinuousConvolution.physical S H
        (GlobalHeatParameter.normalized H hH t) ω) :=
  (MatrixUnboundedContinuousConvolution.continuous_paths S H ω).comp
    (GlobalHeatParameter.continuous_normalized H hH)

theorem remainder_continuous (H : ℝ≥0)
    (ω : RandomInitialBrownianFamily.Space ρ S.law.toMeasure) :
    Continuous (fun t : Time H =>
      MatrixUnboundedCompletedRemainder.value S (toNN H t) ω) := by
  change Continuous (fun t : Time H =>
    MatrixUnboundedGlobalRemainder.value (n := n) (toNN H t) ω.2)
  exact (MatrixUnboundedGlobalRemainder.continuous_paths (n := n) ω.2).comp
    (continuous_clock H)

/-- One null set works for all times in a fixed finite horizon. The
continuous field is exactly the original unbounded global Hilbert
stochastic remainder, rather than a collection of unrelated versions. -/
theorem physical_eq_all (H : ℝ≥0) (hH : 0<H) :
    ∀ᵐ ω ∂μc, ∀ t : Time H,
      MatrixUnboundedContinuousConvolution.physical S H
        (GlobalHeatParameter.normalized H hH t) ω =
      MatrixUnboundedCompletedRemainder.value S (toNN H t) ω := by
  let X : Time H → RandomInitialBrownianFamily.Space ρ S.law.toMeasure → Physical (d := Fin n) :=
    fun t ω => MatrixUnboundedContinuousConvolution.physical S H
      (GlobalHeatParameter.normalized H hH t) ω
  let Y : Time H → RandomInitialBrownianFamily.Space ρ S.law.toMeasure → Physical (d := Fin n) :=
    fun t ω => MatrixUnboundedCompletedRemainder.value S (toNN H t) ω
  have he (t : Time H) : X t =ᵐ[μc] Y t := by
    have h := MatrixUnboundedMildBeforeExit.physical_eq_global_at S H hH
      (toNN H t) t.property.2
    have ht : GlobalHeatRowPhysicalIntegration.unitTime H hH
        (toNN H t) t.property.2 = GlobalHeatParameter.normalized H hH t := by
      apply Subtype.ext
      rfl
    simpa only [X,Y,ht] using h
  have hsim := ContinuousEqualityBeforeExit.simultaneous_clock μc X Y
    (fun _ => (1 : ℝ)) (fun _ : Time H => (0 : ℝ)) continuous_const
    (Filter.Eventually.of_forall (convolution_continuous S H hH))
    (Filter.Eventually.of_forall (remainder_continuous S H))
    (fun t => (he t).mono fun ω hω _ => hω)
  filter_upwards [hsim] with ω hω t
  exact hω t (by norm_num)

/-- The exact mild equation holds simultaneously at all physical
times in each finite horizon, on the completed Brownian space. -/
theorem mild_decomposition_all (H : ℝ≥0) (hH : 0<H) :
    ∀ᵐ ω ∂μc, ∀ t : Time H,
      MatrixUnboundedCompletedGlobal.state S (toNN H t,ω) =
        VectorAnalyticHeat.heat ((toNN H t : ℝ≥0) : ℝ)
          (MatrixGlobalBlockPath.state 1 0 ω.2) +
        MatrixUnboundedContinuousConvolution.physical S H
          (GlobalHeatParameter.normalized H hH t) ω := by
  filter_upwards [physical_eq_all S H hH] with ω hω t
  rw [hω t]
  exact MatrixUnboundedCompletedRemainder.decomposition S (toNN H t) ω

/-- A single null set works for every integer horizon at once. Every
nonnegative physical time lies in one of these horizons, so this is the
global simultaneous version of the stochastic-convolution identity. -/
theorem mild_decomposition_all_natural_horizons :
    ∀ᵐ ω ∂μc, ∀ m : ℕ, ∀ t : Time ((m+1 : ℕ) : ℝ≥0),
      MatrixUnboundedCompletedGlobal.state S
        (toNN ((m+1 : ℕ) : ℝ≥0) t,ω) =
        VectorAnalyticHeat.heat
          ((toNN ((m+1 : ℕ) : ℝ≥0) t : ℝ≥0) : ℝ)
          (MatrixGlobalBlockPath.state 1 0 ω.2) +
        MatrixUnboundedContinuousConvolution.physical S ((m+1 : ℕ) : ℝ≥0)
          (GlobalHeatParameter.normalized ((m+1 : ℕ) : ℝ≥0)
            (by exact_mod_cast Nat.succ_pos m) t) ω := by
  apply ae_all_iff.mpr
  intro m
  exact mild_decomposition_all S ((m+1 : ℕ) : ℝ≥0)
    (by exact_mod_cast Nat.succ_pos m)

end SHEStochastic.MatrixUnboundedMildPath
