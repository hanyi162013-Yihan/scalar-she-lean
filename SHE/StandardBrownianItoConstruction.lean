module
public import SHE.StandardTerminalLevy
public import SHE.StandardTerminalPastLocality
public import SHE.StandardHilbertItoLift
public import SHE.RawCylindricalCoordinates
public import Mathlib.Analysis.InnerProductSpace.l2Space
@[expose] public section
noncomputable section
set_option autoImplicit false
namespace SHE
open MeasureTheory PredictableL2
open scoped NNReal

/-- The ordinary construction component of accepted stochastic input
package1, restricted to GENUINELY RECOGNIZED cylindrical Brownian
coordinates. This is an explicit standard-input predicate, not a theorem
asserting that a terminal isometry determines Brownian stochastic
integration. The total Hilbert basis prevents adding missing noise on
the given sample space. Every scalar coordinate and every Hilbert lift
is tied to the SAME selected integral. No state, heat operator, SPDE,
conditional equation, transition kernel, or uniqueness law occurs here. -/
def StandardBrownianItoConstruction {Ω C ι:Type*}[MeasurableSpace Ω]
    [NormedAddCommGroup C][InnerProductSpace ℝ C][CompleteSpace C]
    [MeasurableSpace C][BorelSpace C][SecondCountableTopology C]
    [Countable ι][DecidableEq ι]
    (𝓕:Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ:Measure Ω)[IsProbabilityMeasure μ](H:ℝ≥0)
    (e:HilbertBasis ι ℝ C) (W:ι→ℝ≥0→Ω→ℝ):Prop:=
  (∀i ω,Continuous (fun t=>W i t ω))→
  (∀i t,Measurable[𝓕 t] (W i t))→
  (∀n (a:Fin n→ι),FiniteBrownianLawOn 𝓕 μ H (fun i=>W (a i))
    (fun i j=>if a i=a j then 1 else 0))→
  ∃J:StandardTerminalIto (C:=C) (E:=ℝ) 𝓕 μ H,
    StandardTerminalPastLocality J ∧ StandardHilbertItoLift J ∧
    ∀i (t:ℝ≥0),t≤H→
      (J.integral (StoppedItoInputs.stop 𝓕 μ H t
        (RawCylindricalCoordinates.row 𝓕 μ H (e:ι→C) i)))=ᵐ[μ] W i t
end SHE
