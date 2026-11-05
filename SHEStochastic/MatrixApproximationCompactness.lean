module

public import SHEStochastic.MatrixSolutionPathTightness
public import SHEStochastic.CanonicalInitialLaw
public import SHEStochastic.MatrixRandomInitialLaw

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
noncomputable section

namespace SHEStochastic.MatrixApproximationCompactness
open MeasureTheory ProbabilityTheory Filter SHE SHE.PredictableL2 SHE.FiniteHaar MatrixInfiniteHaar
open CanonicalStateDriverFiltration
open scoped NNReal ENNReal Topology
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance : Fact (0 < 2*Real.pi) := ⟨by positivity⟩
local instance : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by simp⟩
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {n : ℕ}
local instance : SecondCountableTopology (Physical (d := Fin n)) := Lp.SecondCountableTopology
local instance : MeasurableSpace (Physical (d := Fin n)) := borel _
local instance : BorelSpace (Physical (d := Fin n)) := ⟨rfl⟩
local instance : MeasurableSpace (Input (d := Fin n)) := borel _
local instance : BorelSpace (Input (d := Fin n)) := ⟨rfl⟩
variable (F : Filtration ℝ≥0 mΩ) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
    (hH : (H : ℝ) ≤ 1) (hH0 : 0 < H)
    (G : ℕ → MatrixNonlinearCoefficient.Coefficient (Fin n))
    (N : ℕ → FiniteScalarIto.Family F μ H ((Fin n) × HaarNode))
    (U : ℕ → ℝ≥0 × Ω → Physical (d := Fin n))
    (hU : ∀ m, StronglyMeasurable[F.predictable] (U m))
    (hc : ∀ m ω, Continuous (fun t => U m (t,ω)))
    (u₀ : Physical (d := Fin n))

include hH0 in
/-- Actual bounded-covariance vector approximations have a joint weak
state/noise limit with the prescribed initial state and Brownian drivers
in the full canonical filtration. Passing the nonlinear equation to
this limit remains a separate recognition step. -/
theorem exists_limit (cap : ℝ) (hcap : 0 ≤ cap) (hCaps : ∀ m, NativeMatrixEquation.cap (G m) ≤ cap)
    (hEq : ∀ m, MatrixContinuousMild.Equation (G m) hH (N m) (U m) (hU m) u₀) :
    ∃ Q : ProbabilityMeasure (CanonicalContinuousStateDriver.Space
        (E := Physical (d := Fin n)) (ι := Fin n × HaarNode) H),
      ∃ φ : ℕ → ℕ, StrictMono φ ∧
        Tendsto ((CanonicalApproximationCompactness.varyingLaws F μ H
          (fun m t ω => U m (t,ω)) hc N) ∘ φ) atTop (𝓝 Q) ∧
        (∀ k (a : Fin k → Fin n × HaarNode), FiniteBrownianLawOn
          (filtration (E := Physical (d := Fin n)) (ι := Fin n × HaarNode) H)
          (Q : Measure _) H (fun i => coordinate H (a i))
          (fun i j => if a i = a j then 1 else 0)) ∧
        (Q : Measure _).map (CanonicalInitialLaw.initial H) =
          μ.map (fun _ : Ω => (u₀,fun _ : Fin n × HaarNode => (0 : ℝ))) := by
  have ha (m : ℕ) (t : ℝ≥0) : Measurable[F t] (fun ω => U m (t,ω)) :=
    ((show IsStronglyPredictable F (fun t ω => U m (t,ω)) from hU m).stronglyAdapted t).measurable
  obtain ⟨Q,φ,hφ,hlim,hBrown⟩ := CanonicalApproximationCompactness.exists_limit_varying
    F μ H (fun m t ω => U m (t,ω)) hc ha N
    (MatrixSolutionPathTightness.tight F μ H hH hH0 G N U hU hc u₀ cap hcap hCaps hEq)
  refine ⟨Q,φ,hφ,hlim,hBrown,?_⟩
  apply CanonicalInitialLaw.preserved F μ H (fun m t ω => U m (t,ω)) hc hU N
    (fun _ => u₀) measurable_const _ Q φ hlim
  intro m
  exact MatrixRandomInitialLaw.initial (G m) hH (N m) (U m) (hU m) (fun _ => u₀) (hEq m)

end SHEStochastic.MatrixApproximationCompactness
