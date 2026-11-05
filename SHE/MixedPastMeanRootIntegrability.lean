module

public import SHE.MixedPastMeanAverage
public import SHE.MixedPastMeanTimeFields
public import SHE.UniformRootJets
public import SHE.MeanThetaAverage

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1600000
namespace SHE.MixedPastMeanRootIntegrability
open MeasureTheory PredictableL2 NativeHeatObservation NativeObservationNaturality
  FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation StoppedItoInputs
open scoped NNReal ENNReal
local instance mixedPastMeanRootIntegrability_realSigma : MeasurableSpace RealL2 := borel _
local instance mixedPastMeanRootIntegrability_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance mixedPastMeanRootIntegrability_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance mixedPastMeanRootIntegrability_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance mixedPastMeanRootIntegrability_blockSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance mixedPastMeanRootIntegrability_blockBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
variable {Ω : Type} [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
variable (Λ κ : ℝ) (hκ : 0<κ) {aU aV : ℝ→ℝ} (haU : Measurable aU) (haV : Measurable aV) {ell M : ℝ}
variable (hell : 0<ell) (hbU : ∀ z,ell≤aU z ∧ aU z≤M) (hbV : ∀ z,ell≤aV z ∧ aV z≤M)
variable (I₀ I₁ : StandardTerminalIto (C:=RealHaarIntegrand.Columns) (E:=RealL2) 𝓕 μ H)
variable (u₀ : RealL2)
variable (Pair : MixedNativeAdditiveResidualPair.Solution 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀)
variable (J : StandardTerminalIto (C:=Both RealHaarInput) (E:=ℝ) 𝓕 μ H)
variable (hIJ₀ : StandardScalarNaturality I₀ (leftIntegral 𝓕 μ H J))
variable (hIJ₁ : StandardScalarNaturality I₁ (rightIntegral 𝓕 μ H J))
open Real AddCircle Set Filter WordRecursion ControlledProfile ControlledReferenceLevel SmoothCylinders UniformSmooth
  CutoffWordLevel CutoffWordHistories CutoffCarriers PhysicalScoreChain PhysicalChainArrays
  HistoryProductMeasure ActualMeanKernel
local instance mixedPastMeanRootIntegrability_circleSigma : MeasurableSpace CircleL2 := borel _
local instance mixedPastMeanRootIntegrability_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩
local instance mixedPastMeanRootIntegrability_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
local instance mixedPastMeanRootIntegrability_secondCountable : SecondCountableTopology CircleL2 :=
  (_root_.fourierBasis (T:=2*Real.pi)).repr.toHomeomorph.secondCountableTopology
variable (P : CanonicalCovariance.ProfileParameters) (haP : BoundedSmooth P.coefficient)
variable (v b : ℝ≥0) (hvb : v≤b)
variable (Z : VariableObservations.Family HeatCircle 1)
variable (htarget : ∀ x i,(b:ℝ)≤(Z.observations x i).target)
variable (hstop : ∀ x i,(b:ℝ)≤(Z.observations x i).stop)
variable (F : HeatCircle→WordRecursion.State 1→ℝ) (hF : UniformBoundedSmooth F)
variable (hFm : Measurable (fun z : HeatCircle×WordRecursion.State 1=>F z.1 z.2))
local notation "Input"=>MixedPastMeanInputEnergy.input 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ Pair
  P haP v b hvb Z htarget hstop F hF hFm
local notation "Average"=>MixedPastMeanFields.average 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ Pair
  P haP v b hvb Z htarget hstop F hF hFm
attribute [local irreducible] MixedPastMeanInputEnergy.input MixedPastMeanFields.average

include hIJ₀ hIJ₁ in
/-- Genuine old-time/sample integrability and a uniform theta L² bound
follow from the actual mean estimate for every bounded smooth root.
No additional Bernstein or field-additivity premise is required. -/
theorem uniform_average_bound (hlocal : StandardTerminalPastLocality J) (hΛ : 0<Λ)
    (hages : ∀ x i,(Z.observations x i).stop≤(Z.observations x i).target)
    (hrootStop : ∀ x i,(Z.observations x i).stop≤(b:ℝ))
    (hrootTarget : ∀ x i,(Z.observations x i).target=(b:ℝ))
    (hcenter : ∀ x,(Z.observations x 0).center=x)
    (hspan : (b:ℝ)-(v:ℝ)≤P.horizon) (k : ℕ)
    (hfresh : (b:ℝ)-(v:ℝ)≤UniformFutureProfileScores.horizon (1+k))
    (hold : ∀ j,j<k→(b:ℝ)-(v:ℝ)≤uniformHorizon 1 j)
    (p : ℕ) (hp : 0<p) (B0 : ℝ≥0) (hBDG : StandardTerminalBDGPower ((2*p)*(k+2)) J B0)
    (mass ρ : ℝ) (hmass : 1≤mass) (hρ : 0<ρ) (hρhalf : ρ<1/2)
    (q : ℝ≥0) (hvq : v≤q) (hqb : q<b) (hqH : q≤H) (hq1 : (q:ℝ)≤1) :
    let old:=Measure.pi (fun _ : Fin k=>volume.restrict (Ioc (v:ℝ) (b:ℝ)))
    ∃ C : ℝ,0≤C ∧ ∀ θ : ℝ,|θ|≤1→
      Integrable (fun z : (Fin k→ℝ)×Ω=>Input k θ q mass ρ hmass hρ.le z.1 z.2) (old.prod μ) ∧
      Integrable (fun ω=>‖Average k old θ q mass ρ hmass hρ.le ω‖^2) μ ∧
      (∫ ω,‖Average k old θ q mass ρ hmass hρ.le ω‖^2 ∂μ)≤C := by
  intro old
  obtain ⟨A0,hA0,hjet⟩:=hF.finite_jet_bound k
  let N:=(2*p)*(k+2)
  let CG:=MixedPastWordMoments.momentConstant P k k (2*p)
    ((k:ℝ)*(NativeHybridMoments.momentConstant N B0 κ M)^P.exponent)
  let CD:=MixedHeatedDifferenceMoments.momentConstant N B0 κ M^((1-(0:ℝ))/(k+2:ℝ))
  let C:=((CD+CG)/2)^(1/(p:ℝ))
  let K:=PastMeanRMS.coefficient P k ρ C*((b:ℝ)-q)^(ρ/2)
  let E:=∫ ω,‖Pair.second q ω-Pair.first q ω‖^2 ∂μ
  let B:=(K*E^((0:ℝ)/2)*((4:ℝ)^(0:ℝ)*Λ^(-(0:ℝ)))*
    QuarterRMSTimeFactors.oldTimeBudget P (ControlledOldIntervals.fraction P*P.lower) (uniformConstant 1)
      k ((b:ℝ)-v) ((q:ℝ)-v) (1/2-(0:ℝ)) A0 1)^2
  refine ⟨B,sq_nonneg _,fun θ hθ=>?_⟩
  have hh:=MixedPastMeanAverage.actual_averaged_energy 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ Pair
    J hIJ₀ hIJ₁ P haP v b hvb Z htarget hstop F hF hFm hlocal hΛ hages hrootStop hrootTarget hcenter
    hspan k hfresh hold θ hθ A0 1 hA0 (by norm_num) hjet 0 (by norm_num) (by norm_num)
    p hp (by simpa only [sub_zero,mul_one] using (show (1:ℝ)≤(p:ℝ) from by exact_mod_cast (show 1≤p by omega)))
    B0 hBDG mass ρ hmass hρ hρhalf 0 (by norm_num) (by norm_num) q hvq hqb hqH hq1
  simpa only [MixedPastMeanFields.average] using hh

include hIJ₀ hIJ₁ in
/-- The genuine theta/old-time averaged root field is absolutely
integrable before any finite-cutoff interchange is performed. -/
theorem theta_integrable (hlocal : StandardTerminalPastLocality J) (hΛ : 0<Λ)
    (hages : ∀ x i,(Z.observations x i).stop≤(Z.observations x i).target)
    (hrootStop : ∀ x i,(Z.observations x i).stop≤(b:ℝ))
    (hrootTarget : ∀ x i,(Z.observations x i).target=(b:ℝ))
    (hcenter : ∀ x,(Z.observations x 0).center=x)
    (hspan : (b:ℝ)-(v:ℝ)≤P.horizon) (k : ℕ)
    (hfresh : (b:ℝ)-(v:ℝ)≤UniformFutureProfileScores.horizon (1+k))
    (hold : ∀ j,j<k→(b:ℝ)-(v:ℝ)≤uniformHorizon 1 j)
    (p : ℕ) (hp : 0<p) (B0 : ℝ≥0) (hBDG : StandardTerminalBDGPower ((2*p)*(k+2)) J B0)
    (mass ρ : ℝ) (hmass : 1≤mass) (hρ : 0<ρ) (hρhalf : ρ<1/2)
    (q : ℝ≥0) (hvq : v≤q) (hqb : q<b) (hqH : q≤H) (hq1 : (q:ℝ)≤1) :
    let old:=Measure.pi (fun _ : Fin k=>volume.restrict (Ioc (v:ℝ) (b:ℝ)))
    Integrable (fun z : ℝ×Ω=>Average k old z.1 q mass ρ hmass hρ.le z.2)
      (MeanThetaAverage.thetaMeasure.prod μ) := by
  intro old
  obtain ⟨C,hC,hbound⟩:=uniform_average_bound 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ Pair
    J hIJ₀ hIJ₁ P haP v b hvb Z htarget hstop F hF hFm hlocal hΛ hages hrootStop hrootTarget hcenter
    hspan k hfresh hold p hp B0 hBDG mass ρ hmass hρ hρhalf q hvq hqb hqH hq1
  have hm:=MixedPastMeanFields.average_joint_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ Pair
    P haP v b hvb Z htarget hstop F hF hFm hΛ.le k old q mass ρ hmass hρ.le
  have hb : ∀ᵐ θ ∂MeanThetaAverage.thetaMeasure,
      Integrable (fun ω=>‖Average k old θ q mass ρ hmass hρ.le ω‖^2) μ ∧
      (∫ ω,‖Average k old θ q mass ρ hmass hρ.le ω‖^2 ∂μ)≤(sqrt C)^2 := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with θ hθ
    have hθ1 : |θ|≤1:=abs_le.mpr ⟨by linarith [hθ.1],hθ.2⟩
    simpa only [Real.sq_sqrt hC] using (hbound θ hθ1).2
  exact (HilbertParameterAverage.energy μ MeanThetaAverage.thetaMeasure _ hm (fun _=>sqrt C)
    measurable_const (integrable_const _) (fun _=>sqrt_nonneg _)
    (hb.mono (fun _ h=>h.1)) (hb.mono (fun _ h=>h.2))).1

end SHE.MixedPastMeanRootIntegrability
