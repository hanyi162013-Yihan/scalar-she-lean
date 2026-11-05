module

public import SHE.NativeFirstDampedMild
public import SHE.NativeVolterraFields
public import SHE.NativeDampedHaarInput
public import SHE.NativeDampedObservation
public import SHE.PredictableWeightedAlgebra
public import SHE.HeatObservationUniqueness
public import SHE.NativeObservedVolterra
public import SHE.NativeControlMass

@[expose] public section
set_option autoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section

namespace SHE.NativeFirstDampedEquation
open MeasureTheory Set Filter PredictableL2 NativeHeatObservation NativeObservationNaturality
open FiniteHaar StoppedFourier OrthogonalItoChannels StoppedItoInputs DyadicApproximation
open scoped NNReal ENNReal
local instance : Fact (0<(1:ℝ)):=⟨zero_lt_one⟩
local instance : SecondCountableTopology CircleHeat.CircleL2 :=
  (_root_.fourierBasis (T:=1)).repr.toHomeomorph.secondCountableTopology
local instance : SecondCountableTopology RealL2 :=realCircleIdentification.toHomeomorph.secondCountableTopology
local instance nativePairControlObservation_realSigma : MeasurableSpace RealL2 := borel _
local instance nativePairControlObservation_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance nativePairControlObservation_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance nativePairControlObservation_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance nativePairControlObservation_blockSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance nativePairControlObservation_blockBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
variable {Ω : Type*} [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
variable (Λ κ : ℝ) (hκ : 0<κ) {a : ℝ→ℝ} (ha : Measurable a) {ell M : ℝ}
variable (hell : 0<ell) (hb : ∀ z,ell≤a z ∧ a z≤M)
variable (I₀ I₁ : StandardTerminalIto (C := RealHaarIntegrand.Columns) (E := RealL2) 𝓕 μ H)
variable (u₀ : RealL2)
variable (S : NativeMildFirst.Data 𝓕 μ H κ hκ ha hell hb I₀ I₁ u₀)
variable (J : StandardTerminalIto (C := Both RealHaarInput) (E := ℝ) 𝓕 μ H)
variable (hIJ₀ : StandardScalarNaturality I₀ (leftIntegral 𝓕 μ H J))
variable (hIJ₁ : StandardScalarNaturality I₁ (rightIntegral 𝓕 μ H J))

variable(hΛ:0≤Λ)(hH:(H:ℝ)≤1)
include hIJ₀ hIJ₁ in
/-- The true generic native first solution satisfies the full Hilbert damped
resolvent equation. All positive-gap observations are eliminated internally. -/
theorem equation(q:ℝ≥0)(hq:q≤H):
    S.value q=ᵐ[μ] (fun ω=>
      Real.exp (-Λ*(q:ℝ)) • NativeHeatObservation.heat (q:ℝ) u₀+
        Λ • NativeClock.volterra Λ (fun s=>S.value s ω) q+
        I₀.integral (NativeFirstDampedMild.additive 𝓕 μ H Λ κ hκ hΛ hH q hq) ω+
        I₁.integral (NativeFirstDampedMild.residual 𝓕 μ H Λ κ hκ ha hell hb I₀ I₁ u₀ S hΛ hH q hq) ω):=by
  have hpred:IsStronglyPredictable 𝓕 S.value:=S.predictable
  have hS:Measurable (Function.uncurry S.value):=
    (S.predictable.mono (predictable_le_product 𝓕)).measurable
  have hqS:Measurable (S.value q):=(hpred.stronglyAdapted q).measurable.mono (𝓕.le q) le_rfl
  have hV:=NativeVolterraFields.measurable Λ S.value hS q
  have h0:Measurable (fun ω=>I₀.integral
      (NativeFirstDampedMild.additive 𝓕 μ H Λ κ hκ hΛ hH q hq) ω):=(Lp.stronglyMeasurable _).measurable
  have h1:Measurable (fun ω=>I₁.integral
      (NativeFirstDampedMild.residual 𝓕 μ H Λ κ hκ ha hell hb I₀ I₁ u₀ S hΛ hH q hq) ω):=
    (Lp.stronglyMeasurable _).measurable
  apply HeatObservationUniqueness.ae_eq μ _ _ hqS
    (((measurable_const.add (hV.const_smul Λ)).add h0).add h1)
  intro ε hε x
  have ho:=NativeFirstDampedMild.observed 𝓕 μ H Λ κ hκ ha hell hb I₀ I₁ u₀ S J
    hIJ₀ hIJ₁ hΛ hH q hq (T:=(q:ℝ)+ε) (by linarith) x
  simpa only [show (q:ℝ)+ε-(q:ℝ)=ε by ring,Pi.add_apply,Pi.smul_apply] using ho
end SHE.NativeFirstDampedEquation
