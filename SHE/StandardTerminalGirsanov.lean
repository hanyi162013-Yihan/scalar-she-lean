module
public import SHE.ExponentialChangeMeasure
public import SHE.StandardTerminalLevy
public import SHE.StandardHilbertItoLift
@[expose] public section
noncomputable section
set_option autoImplicit false
namespace SHE
open MeasureTheory PredictableL2 StoppedItoInputs
open scoped NNReal ENNReal

/-- The ordinary drift shift of an actual SAME-J coordinate. The plus
sign corresponds to the density exp(-J(u)-bracket(u)/2). -/
def girsanovShift {Ω C : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup C] [InnerProductSpace ℝ C]
    {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {μ : Measure Ω} {H : ℝ≥0}
    (u R : Process (E:=C) 𝓕 μ H) (X : ℝ≥0→Ω→ℝ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  X t ω + ∫s,inner ℝ (R (s,ω)) (u (s,ω)) ∂timeMeasure (min t H)

/-- Accepted temporary external package 7: ordinary finite-dimensional
Girsanov for continuous original Itô coordinates and a bounded-energy
predictable control. Its conclusion concerns only the shifted cylindrical
noise. It contains no heat equation, solution law, approximation limit,
comparison estimate or continuation assertion. -/
def StandardTerminalGirsanovLaw {Ω C : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup C] [InnerProductSpace ℝ C]
    {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {μ : Measure Ω} {H : ℝ≥0}
    (J : StandardTerminalIto (C:=C) (E:=ℝ) 𝓕 μ H) : Prop :=
  ∀ (u : Process (E:=C) 𝓕 μ H),
    (∀ᵐω∂μ,StochasticExponential.bracket 𝓕 μ H u ω≤1) →
    ∀ (n : ℕ) (R : Fin n→Process (E:=C) 𝓕 μ H)
      (X : Fin n→ℝ≥0→Ω→ℝ) (G : Matrix (Fin n) (Fin n) ℝ),
    (∀i,StronglyMeasurable[𝓕.predictable] (Function.uncurry (X i))) →
    (∀i ω,Continuous (fun t=>X i t ω)) →
    (∀t:ℝ≥0,t≤H→∀ᵐω∂μ,∀i:Fin n,
      X i t ω=J.integral (stop 𝓕 μ H t (R i)) ω) →
    (∀ᵐp∂energyMeasure μ H,∀i j:Fin n,inner ℝ (R i p) (R j p)=G i j) →
    FiniteBrownianLawOn 𝓕
      (ExponentialChangeMeasure.measure μ (fun ω=>J.integral u ω)
        (StochasticExponential.bracket 𝓕 μ H u)) H
      (fun i=>girsanovShift u (R i) (X i)) G

/-- The ordinary change-of-integral part of the SAME package 7. The
integrands are actual predictable L2 classes for both equivalent
measures. This interface contains no SPDE or coefficient law. -/
def StandardTerminalGirsanovTransport {Ω C : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup C] [InnerProductSpace ℝ C]
    {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {μ : Measure Ω} {H : ℝ≥0}
    (J : StandardTerminalIto (C:=C) (E:=ℝ) 𝓕 μ H) : Prop :=
  ∀ (u : Process (E:=C) 𝓕 μ H),
    (∀ᵐω∂μ,StochasticExponential.bracket 𝓕 μ H u ω≤1) →
    let Q:=ExponentialChangeMeasure.measure μ (fun ω=>J.integral u ω)
      (StochasticExponential.bracket 𝓕 μ H u)
    ∃ K : StandardTerminalIto (C:=C) (E:=ℝ) 𝓕 Q H,
      ∀ (f : Process (E:=C) 𝓕 μ H) (g : Process (E:=C) 𝓕 Q H),
        (∀ᵐp∂energyMeasure μ H,f p=g p) →
        (∀ᵐω∂Q,K.integral g ω=J.integral f ω+
          ∫s,inner ℝ (f (s,ω)) (u (s,ω)) ∂timeMeasure H)

/-- The authorized temporary seventh stochastic input is precisely
ordinary cylindrical Girsanov: noise-law recognition and transport of
ordinary stochastic integrals under its exponential measure. All heat,
control applicability, solution-law and limiting arguments are external
to this structure and must be proved internally. -/
structure StandardTerminalGirsanov {Ω C : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup C] [InnerProductSpace ℝ C]
    {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {μ : Measure Ω} {H : ℝ≥0}
    (J : StandardTerminalIto (C:=C) (E:=ℝ) 𝓕 μ H) : Prop where
  finiteLaw : StandardTerminalGirsanovLaw J
  transport : StandardTerminalGirsanovTransport J
  /-- Ordinary Hilbert Itô realization under the changed probability,
  within the same temporary Girsanov input. Scalar and Hilbert maps
  share the actual changed cylindrical noise. -/
  hilbertTransport : ∀ (u : Process (E:=C) 𝓕 μ H),
    (∀ᵐω∂μ,StochasticExponential.bracket 𝓕 μ H u ω≤1) →
    let Q:=ExponentialChangeMeasure.measure μ (fun ω=>J.integral u ω)
      (StochasticExponential.bracket 𝓕 μ H u)
    ∀ K : StandardTerminalIto (C:=C) (E:=ℝ) 𝓕 Q H, StandardHilbertItoLift K
end SHE
