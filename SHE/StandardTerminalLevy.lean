module
public import SHE.StandardTerminalIto
public import SHE.StoppedItoInputs
public import SHE.GaussianIncrement
public import Mathlib.Probability.Independence.Basic
public import Mathlib.Probability.HasLaw
@[expose] public section
noncomputable section
set_option autoImplicit false
namespace SHE
open MeasureTheory ProbabilityTheory PredictableL2 StoppedItoInputs
open scoped NNReal ENNReal

/-- Ordinary finite-dimensional Brownian law on the supplied terminal
interval. The time covariance retains every individual observation time.
This is a law statement, not an SPDE existence or uniqueness premise. -/
def FiniteBrownianLawOn {Ω:Type*}[MeasurableSpace Ω]
    (𝓕:Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ:Measure Ω) (H:ℝ≥0)
    {n:ℕ}(X:Fin n→ℝ≥0→Ω→ℝ) (G:Matrix (Fin n) (Fin n) ℝ):Prop:=
  (∀t:Fin n→ℝ≥0,(∀i,t i≤H)→
    HasLaw (fun ω=>WithLp.toLp 2 (fun i=>X i (t i) ω))
      (multivariateGaussian (0:WordRecursion.State n)
        (fun i j=>(min (t i) (t j):ℝ≥0)*G i j)) μ) ∧
  (∀s t:ℝ≥0,s≤t→t≤H→
    Indep (MeasurableSpace.comap (fun ω=>WithLp.toLp 2 (fun i=>X i t ω-X i s ω))
      (inferInstance:MeasurableSpace (WordRecursion.State n))) (𝓕 s) μ)

/-- Accepted external stochastic package5: ordinary finite-dimensional
Levy characterization applied to actual predictable integral rows. It
recognizes continuous SAME-J versions with a deterministic Gram matrix.
No heat profile, SPDE law, transition kernel or continuation is input.
This property is EXTERNAL; it is not derived from terminal isometry. -/
def StandardTerminalLevy {Ω C:Type*}[MeasurableSpace Ω]
    [NormedAddCommGroup C][InnerProductSpace ℝ C]
    {𝓕:Filtration ℝ≥0 ‹MeasurableSpace Ω›}{μ:Measure Ω}{H:ℝ≥0}
    (J:StandardTerminalIto (C:=C) (E:=ℝ) 𝓕 μ H):Prop:=
  ∀(n:ℕ) (R:Fin n→Process (E:=C) 𝓕 μ H)
    (X:Fin n→ℝ≥0→Ω→ℝ) (G:Matrix (Fin n) (Fin n) ℝ),
    (∀i,StronglyMeasurable[𝓕.predictable] (Function.uncurry (X i)))→
    (∀i ω,Continuous (fun t=>X i t ω))→
    (∀t:ℝ≥0,t≤H→∀ᵐω∂μ,∀i:Fin n,X i t ω=J.integral (stop 𝓕 μ H t (R i)) ω)→
    (∀ᵐp∂energyMeasure μ H,∀i j:Fin n,inner ℝ (R i p) (R j p)=G i j)→
    FiniteBrownianLawOn 𝓕 μ H X G
end SHE
