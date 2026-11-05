module
public import SHE.CanonicalFiberLocalUniqueness
public import SHE.StandardHilbertItoLift
public import SHE.NativeSingleNoiseBasis
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1900000
namespace SHE.ConditionalCanonicalModelFamily
open MeasureTheory ProbabilityTheory PredictableL2 FiniteHaar DyadicApproximation
open scoped NNReal ENNReal
local instance : Fact (0<(1:ℝ)) := ⟨zero_lt_one⟩
local instance : SecondCountableTopology CircleHeat.CircleL2 :=
  (_root_.fourierBasis (T:=(1:ℝ))).repr.toHomeomorph.secondCountableTopology
local instance : SecondCountableTopology RealL2 :=
  realCircleIdentification.toHomeomorph.secondCountableTopology
local instance : MeasurableSpace RealL2 := borel _
local instance : BorelSpace RealL2 := ⟨rfl⟩
local instance : MeasurableSpace RealHaarInput := borel _
local instance : BorelSpace RealHaarInput := ⟨rfl⟩
abbrev Space (H:ℝ≥0) := CanonicalContinuousStateDriver.Space (E:=RealL2) (ι:=HaarNode) H
abbrev filtration (H:ℝ≥0) := CanonicalStateDriverFiltration.filtration (E:=RealL2) (ι:=HaarNode) H
abbrev state (H:ℝ≥0) := CanonicalStateDriverFiltration.state (E:=RealL2) (ι:=HaarNode) H

/-- A supplied canonical conditional model with its recognized SAME
white integral retained. Every field is actual stochastic/model data;
no equality of solution laws occurs in this packet. -/
structure Packet (H:ℝ≥0) (D:SmoothApproximation.ScalarData)
    (ν:Measure (Space H)) [IsProbabilityMeasure ν] (u₀:RealL2) where
  white : StandardTerminalIto (C:=RealHaarInput) (E:=ℝ) (filtration H) ν H
  locality : StandardTerminalPastLocality white
  hilbert : StandardHilbertItoLift white
  basis_ids : ∀i (t:ℝ≥0), t≤H→
    (white.integral (StoppedItoInputs.stop (filtration H) ν H t
      (RawCylindricalCoordinates.row (filtration H) ν H
        (NativeSingleNoiseBasis.basis:HaarNode→RealHaarInput) i)))=ᵐ[ν]
      CanonicalStateDriverFiltration.coordinate H i t
  model : SingleNativeHeatEquation.Data (filtration H) ν H D
    (NativeWhiteToPhysicalEquation.physical (filtration H) ν H white) u₀
  model_eq : model.value=state H

section Family
variable {P:Type*} {ι:Type} [MeasurableSpace P] [Fintype ι]
variable (H:ℝ≥0) (D:SmoothApproximation.ScalarData)
variable (κ:ι→Kernel P (Space H)) [∀i,IsMarkovKernel (κ i)]
variable (ρ:Measure P) (known:P→RealL2)

/-- Exactly the existing seven ordinary input record on the selected
physical maps/models. In particular, this contains no local-uniqueness
or conditional future-law assumption. -/
abbrev OrdinaryInputs (p:P) (A:∀i,Packet H D (κ i p) (known p)) :=
  GivenSingleNativeArbitraryLocalUniqueness.Inputs (ι:=ι) (fun _:ι=>Space H)
    (fun _:ι=>filtration H) (fun i:ι=>κ i p) H D
    (fun i:ι=>NativeWhiteToPhysicalEquation.physical (filtration H) (κ i p) H (A i).white)
    (known p) (fun i:ι=>(A i).model)

/-- Conditional state laws coincide on ONE common prefix event. The
model packets may be chosen only after that event has been established;
only the existing ordinary stochastic-input record is selected there. -/
theorem state_laws_eq (hH:0<H) (hH1:(H:ℝ)≤1)
    (hPackets:∀i,∀ᵐp∂ρ,Nonempty (Packet H D (κ i p) (known p)))
    (hSelector:∀p (A:∀i,Packet H D (κ i p) (known p)),Nonempty (OrdinaryInputs H D κ known p A)):
    ∀ᵐp∂ρ,∀i j:ι,(κ i p).map Prod.fst=(κ j p).map Prod.fst :=by
  filter_upwards [ae_all_iff.mpr hPackets] with p hp
  let A:∀i,Packet H D (κ i p) (known p):=fun i=>Classical.choice (hp i)
  let inputs:OrdinaryInputs H D κ known p A:=Classical.choice (hSelector p A)
  exact CanonicalFiberLocalUniqueness.state_laws_eq (ι:=ι) H D (fun i:ι=>κ i p)
    (fun i:ι=>(A i).white) (known p) (fun i:ι=>(A i).model) hH hH1
    (fun i:ι=>(A i).model_eq) inputs
/-- Ordinary inputs are required only on the genuine common-prefix
almost-everywhere event; exceptional non-Brownian fibers are unused. -/
theorem state_laws_eq_ae (hH:0<H) (hH1:(H:ℝ)≤1)
    (hPackets:∀i,∀ᵐp∂ρ,Nonempty (Packet H D (κ i p) (known p)))
    (hSelector:∀ᵐp∂ρ,∀A:∀i,Packet H D (κ i p) (known p),
      Nonempty (OrdinaryInputs H D κ known p A)):
    ∀ᵐp∂ρ,∀i j:ι,(κ i p).map Prod.fst=(κ j p).map Prod.fst :=by
  filter_upwards [ae_all_iff.mpr hPackets,hSelector] with p hp hs
  let A:∀i,Packet H D (κ i p) (known p):=fun i=>Classical.choice (hp i)
  let inputs:OrdinaryInputs H D κ known p A:=Classical.choice (hs A)
  exact CanonicalFiberLocalUniqueness.state_laws_eq (ι:=ι) H D (fun i:ι=>κ i p)
    (fun i:ι=>(A i).white) (known p) (fun i:ι=>(A i).model) hH hH1
    (fun i:ι=>(A i).model_eq) inputs
end Family
end SHE.ConditionalCanonicalModelFamily
