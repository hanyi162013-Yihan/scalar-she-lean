module
public import SHE.MixedCappedControl
public import SHE.CappedGirsanovDriver
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
namespace SHE.MixedCappedGirsanovDriver
open MeasureTheory PredictableL2 NativeHeatObservation NativeObservationNaturality
open FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation StoppedItoInputs
open scoped NNReal ENNReal
local instance :Fact (0<2*Real.pi):=⟨by positivity⟩
local instance :Fact ((2:ENNReal)≠⊤):=⟨by simp⟩
local instance :MeasurableSpace RealL2:=borel _
local instance :BorelSpace RealL2:=⟨rfl⟩
local instance :MeasurableSpace CircleL2:=borel _
local instance :BorelSpace CircleL2:=⟨rfl⟩
local instance :MeasurableSpace RealHaarInput:=borel _
local instance :BorelSpace RealHaarInput:=⟨rfl⟩
local instance :MeasurableSpace (Both RealHaarInput):=borel _
local instance :BorelSpace (Both RealHaarInput):=⟨rfl⟩
local instance :MeasurableSpace RealHaarIntegrand.Columns:=borel _
local instance :BorelSpace RealHaarIntegrand.Columns:=⟨rfl⟩
variable {Ω ι:Type}[MeasurableSpace Ω][Countable ι][DecidableEq ι]
variable (𝓕:Filtration ℝ≥0 ‹MeasurableSpace Ω›)(μ:Measure Ω)[IsProbabilityMeasure μ](H:ℝ≥0)
variable (Λ κ:ℝ)(hκ:0<κ){aU aV:ℝ→ℝ}(haU:Measurable aU)(haV:Measurable aV){ell M:ℝ}
variable (hell:0<ell)(hbU:∀z,ell≤aU z ∧ aU z≤M)(hbV:∀z,ell≤aV z ∧ aV z≤M)
variable (I₀ I₁:StandardTerminalIto (C:=RealHaarIntegrand.Columns) (E:=RealL2) 𝓕 μ H)
variable (u₀:RealL2)
variable (S:MixedNativeAdditiveResidualPair.Solution 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀)
variable (J:StandardTerminalIto (C:=Both RealHaarInput) (E:=ℝ) 𝓕 μ H)
variable (hIJ₀:StandardScalarNaturality I₀ (leftIntegral 𝓕 μ H J))
variable (hIJ₁:StandardScalarNaturality I₁ (rightIntegral 𝓕 μ H J))
local notation "Raw"=>MixedCappedControl.raw 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
local notation "Global"=>MixedMovingEnergy.globalEnergy 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
local notation "Rows"=>CappedGirsanovDriver.originalRow 𝓕 μ H
local notation "Coordinates"=>CappedGirsanovDriver.originalCoordinate 𝓕 μ H J
include hIJ₀ hIJ₁

/-- The actual coupling's raw additive control supplies the same
capped input, literal bracket, changed scalar integral, and shifted
driver law. All exit and entropy bounds use its exact true energy
Lambda^2/kappa times Global, without a canonical SPDE law premise. -/
theorem exists_changed_driver(e:ι→Both RealHaarInput)(he:Orthonormal ℝ e)
    (hNovikov:StandardTerminalNovikov J)(hGirsanov:StandardTerminalGirsanov J)
    (hΛ:0≤Λ)(hH:(H:ℝ)≤1)(hH0:0<H)
    (hnull:NullCompleteFiltration.ContainsNullSets 𝓕 μ)
    (B1 B16:ℝ≥0)(hBDG1:StandardTerminalBDGPower 1 J B1)(hBDG16:StandardTerminalBDG16 J B16):
    ∃u:Process (E:=Both RealHaarInput) 𝓕 μ H,
      u=ᵐ[energyMeasure μ H] Function.uncurry (PredictableEnergyCap.capped Raw) ∧
      (∀ᵐω∂μ,StochasticExponential.bracket 𝓕 μ H u ω≤1) ∧
      let Q:=ExponentialChangeMeasure.measure μ (fun ω=>J.integral u ω)
        (StochasticExponential.bracket 𝓕 μ H u)
      let cost:=(Λ^2/κ)*Global
      IsProbabilityMeasure Q ∧ μ≪Q ∧ Q≪μ ∧
      CylindricalDriverLaw.Law Q H (fun i=>girsanovShift u (Rows e i) (Coordinates e i)) ∧
      (∀i t,Measurable (girsanovShift u (Rows e i) (Coordinates e i) t)) ∧
      (∃K:StandardTerminalIto (C:=Both RealHaarInput) (E:=ℝ) 𝓕 Q H,
        ∀(f:Process (E:=Both RealHaarInput) 𝓕 μ H)(g:Process (E:=Both RealHaarInput) 𝓕 Q H),
          (∀ᵐp∂energyMeasure μ H,f p=g p)→
          (∀ᵐω∂Q,K.integral g ω=J.integral f ω+
            ∫s,inner ℝ (f (s,ω)) (u (s,ω)) ∂timeMeasure H)) ∧
      μ.real {ω|1≤PredictableEnergyCap.accumulated Raw H ω}≤cost ∧
      (∀(f:Ω→ℝ)(B:ℝ),AEStronglyMeasurable f μ→0≤B→(∀ω,|f ω|≤B)→
        |(∫ω,f ω ∂Q)-(∫ω,f ω ∂μ)|≤2*B*Real.sqrt cost) ∧
      (∀(f g:Ω→ℝ)(B:ℝ),AEStronglyMeasurable f μ→AEStronglyMeasurable g μ→
        0≤B→(∀ω,|f ω|≤B)→(∀ω,|g ω|≤B)→
        (∀ω,ω∉{ω|1≤PredictableEnergyCap.accumulated Raw H ω}→f ω=g ω)→
        |(∫ω,f ω ∂μ)-(∫ω,g ω ∂Q)|≤2*B*(Real.sqrt cost+cost)):=by
  have hd:=MixedMovingEnergy.global_integrable
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S J hIJ₀ hIJ₁ hΛ hH B1 hBDG1
  have hi:Integrable (fun p:ℝ≥0×Ω=>‖Raw p.1 p.2‖^2) (energyMeasure μ H):=by
    convert! hd.const_mul (Λ^2/κ) using 1
    funext p
    exact MixedCappedControl.norm_sq 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S p
  have hw:=CappedGirsanovDriver.exists_changed_driver 𝓕 μ H J Raw
    (MixedCappedControl.adapted 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S)
    (MixedCappedControl.continuous 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S)
    e he hNovikov hGirsanov hH hH0 hnull B16 hBDG16 hi
  simpa only [MixedCappedControl.energy 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S] using hw

end SHE.MixedCappedGirsanovDriver
