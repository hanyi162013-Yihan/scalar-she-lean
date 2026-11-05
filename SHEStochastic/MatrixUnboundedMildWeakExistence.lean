module

public import SHEStochastic.MatrixUnboundedMildBeforeExit
public import SHEStochastic.MatrixUnboundedMildPath

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 900000
noncomputable section

namespace SHEStochastic.MatrixUnboundedMildWeakExistence
open MeasureTheory SHE Matrix MatrixInfiniteHaar HeatParameterCover HeatParameterCoordinates
open GlobalHeatRowPhysicalIntegration
open scoped NNReal ENNReal Matrix.Norms.L2Operator MatrixOrder
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance : Fact (0 < 2*Real.pi) := ⟨by positivity⟩
local instance : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by simp⟩
variable {n : ℕ}
local instance : SecondCountableTopology (Physical (d := Fin n)) := Lp.SecondCountableTopology
local instance : MeasurableSpace (Physical (d := Fin n)) := borel _
local instance : BorelSpace (Physical (d := Fin n)) := ⟨rfl⟩

/-- The global unbounded matrix equation also starts from any square-integrable
law. Its initial marginal is the prescribed law, its original Fourier
equation holds on every finite horizon, and one null set per horizon
supports the entire continuous Hilbert-valued mild path. -/
theorem exists_random_initial_pathwise
    (G : EuclideanSpace ℝ (Fin n) → Matrix (Fin n) (Fin n) ℝ)
    {C β : ℝ≥0} (hG : HolderWith C β G) (hβ : 0<β) (hβ1 : β<1)
    (ρ₀ : MatrixLocalBlockChain.L2Law (n := n))
    (ell : ℝ) (hell : 0<ell)
    (hLower : ∀ z,ell • (1 : Matrix (Fin n) (Fin n) ℝ)≤G z*(G z)ᴴ) :
    ∃ R : MatrixUnboundedGlobalFourierAll.FullSolution G hG hβ hβ1 ρ₀,
      R.base.law.toMeasure.map (MatrixGlobalBlockPath.state 1 0)=ρ₀.val.toMeasure ∧
      ∀ (H : ℝ≥0) (hH : 0<H),
        ∀ᵐ ω ∂IndependentNoiseCompletion.measure (Measure.dirac ()) R.base.law.toMeasure,
          ∀ t : StoppedPathPasting.Time H,
            MatrixUnboundedCompletedGlobal.state R.base
              (AdaptedCanonicalPathTests.toNN H t,ω) =
              VectorAnalyticHeat.heat
                ((AdaptedCanonicalPathTests.toNN H t : ℝ≥0) : ℝ)
                (MatrixGlobalBlockPath.state 1 0 ω.2) +
              MatrixUnboundedContinuousConvolution.physical R.base H
                (GlobalHeatParameter.normalized H hH t) ω := by
  obtain ⟨R⟩ := MatrixUnboundedGlobalFourierAll.exists_full_solution
    G hG hβ hβ1 ρ₀ ell hell hLower
  exact ⟨R, R.base.initial,
    fun H hH => MatrixUnboundedMildPath.mild_decomposition_all R.base H hH⟩

/-- From any deterministic vector L2 datum, the original unbounded
uniformly elliptic matrix SPDE admits one global weak solution with a
continuous Hilbert-valued stochastic heat convolution. At each prescribed
positive time, the convolution is identified almost surely with the
state-minus-heat remainder on the same Brownian probability space. -/
theorem exists_deterministic
    (G : EuclideanSpace ℝ (Fin n) → Matrix (Fin n) (Fin n) ℝ)
    {C β : ℝ≥0} (hG : HolderWith C β G) (hβ : 0<β) (hβ1 : β<1)
    (u₀ : Physical (d := Fin n)) (ell : ℝ) (hell : 0<ell)
    (hLower : ∀ z,ell • (1 : Matrix (Fin n) (Fin n) ℝ)≤G z*(G z)ᴴ) :
    ∃ S : MatrixUnboundedGlobalWeakExistence.Solution G hG hβ hβ1
        (MatrixUnboundedGlobalFourierAll.pointLaw u₀),
      (MatrixGlobalBlockPath.state 1 0 =ᵐ[S.law.toMeasure] fun _ => u₀) ∧
      ∀ (H : ℝ≥0) (hH : 0<H),
        (fun ω => MatrixUnboundedCompletedGlobal.state S (H,ω)) =ᵐ[
          IndependentNoiseCompletion.measure (Measure.dirac ()) S.law.toMeasure]
          fun ω => VectorAnalyticHeat.heat (H : ℝ)
            (MatrixGlobalBlockPath.state 1 0 ω.2) +
            MatrixUnboundedContinuousConvolution.physical S H
              (unitTime H hH H le_rfl) ω := by
  obtain ⟨R⟩ := MatrixUnboundedGlobalFourierAll.exists_deterministic_full_solution
    G hG hβ hβ1 u₀ ell hell hLower
  exact ⟨R.base, MatrixUnboundedDeterministicMild.initial_ae u₀ R.base,
    fun H hH => MatrixUnboundedMildBeforeExit.mild_decomposition R.base H hH⟩

/-- Stronger pathwise formulation: for each chosen finite horizon, one
null set suffices for the whole continuous vector mild path, including
time zero. No additional stochastic-analysis premise is introduced. -/
theorem exists_deterministic_pathwise
    (G : EuclideanSpace ℝ (Fin n) → Matrix (Fin n) (Fin n) ℝ)
    {C β : ℝ≥0} (hG : HolderWith C β G) (hβ : 0<β) (hβ1 : β<1)
    (u₀ : Physical (d := Fin n)) (ell : ℝ) (hell : 0<ell)
    (hLower : ∀ z,ell • (1 : Matrix (Fin n) (Fin n) ℝ)≤G z*(G z)ᴴ) :
    ∃ S : MatrixUnboundedGlobalWeakExistence.Solution G hG hβ hβ1
        (MatrixUnboundedGlobalFourierAll.pointLaw u₀),
      (MatrixGlobalBlockPath.state 1 0 =ᵐ[S.law.toMeasure] fun _ => u₀) ∧
      ∀ (H : ℝ≥0) (hH : 0<H),
        ∀ᵐ ω ∂IndependentNoiseCompletion.measure (Measure.dirac ()) S.law.toMeasure,
          ∀ t : StoppedPathPasting.Time H,
            MatrixUnboundedCompletedGlobal.state S
              (AdaptedCanonicalPathTests.toNN H t,ω) =
              VectorAnalyticHeat.heat
                ((AdaptedCanonicalPathTests.toNN H t : ℝ≥0) : ℝ)
                (MatrixGlobalBlockPath.state 1 0 ω.2) +
              MatrixUnboundedContinuousConvolution.physical S H
                (GlobalHeatParameter.normalized H hH t) ω := by
  obtain ⟨R⟩ := MatrixUnboundedGlobalFourierAll.exists_deterministic_full_solution
    G hG hβ hβ1 u₀ ell hell hLower
  exact ⟨R.base, MatrixUnboundedDeterministicMild.initial_ae u₀ R.base,
    fun H hH => MatrixUnboundedMildPath.mild_decomposition_all R.base H hH⟩

end SHEStochastic.MatrixUnboundedMildWeakExistence
