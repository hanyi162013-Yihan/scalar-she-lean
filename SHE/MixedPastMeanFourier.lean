module

public import SHE.FamilyMeanCoordinates
public import SHE.MixedPastMeanLegIdentity
public import SHE.NativeFourierAverage
public import SHE.MixedPastMeanSupport
public import SHE.MixedPastSpatialMoments
public import SHE.ControlledFamilyMeanFields
public import SHE.MixedPastKernelSections
public import SHE.ControlledFamilyMeanEnergy
public import SHE.ControlledFamilyMeanFirstMoment
public import SHE.PastMeanAbsoluteBudget
public import SHE.MixedPastMeanFirstMoment
public import SHE.MixedPastBaselineFTCIdentity

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3600000
set_option quotPrecheck false

namespace SHE.MixedPastMeanFourier
open MeasureTheory PredictableL2 NativeHeatObservation NativeObservationNaturality
  FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation StoppedItoInputs
open scoped NNReal ENNReal
local instance mixedPastMeanFourier_realSigma : MeasurableSpace RealL2 := borel _
local instance mixedPastMeanFourier_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance mixedPastMeanFourier_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance mixedPastMeanFourier_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance mixedPastMeanFourier_blockSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance mixedPastMeanFourier_blockBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
variable {Ω : Type} [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
variable (Λ κ : ℝ) (hκ : 0<κ) {aU aV : ℝ→ℝ} (haU : Measurable aU) (haV : Measurable aV) {ell M : ℝ}
variable (hell : 0<ell) (hbU : ∀ z,ell≤aU z ∧ aU z≤M) (hbV : ∀ z,ell≤aV z ∧ aV z≤M)
variable (I₀ I₁ : StandardTerminalIto (C:=RealHaarIntegrand.Columns) (E:=RealL2) 𝓕 μ H)
variable (u₀ : RealL2)
variable (S : MixedNativeAdditiveResidualPair.Solution 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀)
variable (J : StandardTerminalIto (C:=Both RealHaarInput) (E:=ℝ) 𝓕 μ H)
variable (hIJ₀ : StandardScalarNaturality I₀ (leftIntegral 𝓕 μ H J))
variable (hIJ₁ : StandardScalarNaturality I₁ (rightIntegral 𝓕 μ H J))
open Real AddCircle Set Filter WordRecursion ControlledProfile ControlledReferenceLevel SmoothCylinders UniformSmooth
  CutoffWordLevel CutoffWordHistories CutoffCarriers PhysicalScoreChain PhysicalChainArrays
  PhysicalParentGeometry CoveredHistoryGeometry CoveredControlledLaw ControlledOldIntervals
  HistoryProductMeasure ActualMeanKernel
local instance mixedPastMeanFourier_circleSigma : MeasurableSpace CircleL2 := borel _
local instance mixedPastMeanFourier_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩
local instance mixedPastMeanFourier_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
variable (P : CanonicalCovariance.ProfileParameters) (haP : BoundedSmooth P.coefficient)
variable (v b : ℝ≥0) (hvb : v≤b)
variable (Z : VariableObservations.Family HeatCircle 1)
variable (htarget : ∀ x i,(b:ℝ)≤(Z.observations x i).target)
variable (hstop : ∀ x i,(b:ℝ)≤(Z.observations x i).stop)
variable (F : HeatCircle→WordRecursion.State 1→ℝ) (hF : UniformBoundedSmooth F)
variable (hFm : Measurable (fun z : HeatCircle×WordRecursion.State 1=>F z.1 z.2))
local notation "Base" => ControlledReferenceThetaGeometry.level P P.coefficient haP Λ v b hvb Z htarget hstop F hF hFm
local notation "Zero" => Base (0,(0,0))
local notation "U" => MixedPastJointData.pastU 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S v
local notation "Dir" => MixedPastJointData.pastD 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S v
local notation "Mean" => MixedPastLiteralPoint.meanField 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S P haP v b hvb Z htarget hstop F hF hFm

open NativeRandomKernel NormalizedKernelSplit QuarterSpatialEvent
local notation "Ref" => (fun a : ℝ×Inputs=>referenceData P P.coefficient haP Λ a.1 v b hvb a.2)

local notation "Input"=>MixedPastMeanInputEnergy.input 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
  P haP v b hvb Z htarget hstop F hF hFm
local notation "Leg"=>MixedPastMeanLegIdentity.leg 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
  P haP v b hvb Z htarget hstop F hF hFm
attribute [local irreducible] MixedPastLiteralPoint.meanField MixedPastJointData.pastU MixedPastJointData.pastD

/-- The actual physical mean mark and the previously bounded Hilbert
input have exactly the same weighted Fourier coordinates at each active
old-time section, with all original stop weights retained. -/
theorem input_fourier (hΛ : 0≤Λ)
    (hages : ∀ x i,(Z.observations x i).stop≤(Z.observations x i).target)
    (hrootStop : ∀ x i,(Z.observations x i).stop≤(b:ℝ))
    (k : ℕ) (θ : ℝ) (q : ℝ≥0) (hvq : v≤q)
    (mass ρ : ℝ) (hmass : 1≤mass) (hρ : 0≤ρ)
    (t : Fin k→ℝ) (hq : (q:ℝ)<fixedTerminal (R:=Ref (0,(0,0))) (b:ℝ) k t)
    (ω : Ω) (n : ℤ) :
    fourierCoeff (Input k θ q mass ρ hmass hρ t ω) n=
      (((mass+(n:ℝ)^2)^(-ρ/2):ℝ):ℂ)*fourierCoeff
        (fun x=>Complex.ofReal (∫ y : Fin k→HeatCircle,Leg k θ q (separated k (x,t,y)) ω
          ∂Measure.pi (fun _=>haarAddCircle))) n := by
  let a : ℝ×Inputs:=(θ,(U ω,Dir ω))
  let m : Unit→History HeatCircle k→WordRecursion.State (1+k):=fun _=>Mean k θ q ω
  have hm : ∀ z : Unit,Measurable (m z) := by
    intro z
    change Measurable (Mean k θ q ω)
    have hme : Measurable (fun z : Ω×History HeatCircle k=>Mean k θ q z.1 z.2):=
      MixedPastLiteralFields.meanField_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S
        P haP v b hvb Z htarget hstop F hF hFm k θ q
    exact hme.comp (show Measurable (fun p : History HeatCircle k=>(ω,p)) from
      measurable_const.prodMk measurable_id)
  have hfixed : ∀ j (t : Fin j→ℝ),
      fixedTerminal (R:=Ref a) (b:ℝ) j t=fixedTerminal (R:=Ref (0,(0,0))) (b:ℝ) j t := by
    intro j
    induction j with
    | zero => intro t;rfl
    | succ j ih =>
      intro t
      simp only [fixedTerminal,ih]
      rfl
  have hq' : (q:ℝ)<fixedTerminal (R:=Ref a) (b:ℝ) k t := by rw [hfixed];exact hq
  have hh:=familyMeanInput_fourier Ref Base (fun _ : Unit=>a) k mass ρ hmass hρ
    (fun _=>Λ) (fun _=>(q:ℝ)) (fun _=>(b:ℝ)) (fun _ _=>rfl) (fun _=>hΛ)
    m hm (fun _=>t) (fun _=>hq') (fun _=>S.second q ω-S.first q ω) () n
  change fourierCoeff (Input k θ q mass ρ hmass hρ t ω) n=_ at hh
  rw [hh]
  congr 1
  apply congrArg (fun g : HeatCircle→ℂ=>fourierCoeff g n)
  funext x
  unfold familyMeanCoordinate
  apply congrArg Complex.ofReal
  apply integral_congr_ae
  filter_upwards with y
  let p:=separated k (x,t,y)
  have hp : (q:ℝ)<(carrier Zero k).terminal p := by
    rw [show (carrier Zero k).terminal p=fixedTerminal (R:=Ref (0,(0,0))) (b:ℝ) k t from
      terminal_separated Zero (b:ℝ) (fun _=>rfl) k t x y]
    exact hq
  rw [MixedPastMeanLegIdentity.leg_eq_value 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
    P haP v b hvb Z htarget hstop F hF hFm hages hrootStop k θ q hvq p hp ω]
  have ht:=ControlledReferenceThetaGeometry.carrier_terminal_eq P P.coefficient haP Λ v b hvb
    Z htarget hstop F hF hFm a (0,(0,0)) k p
  have ho:=ControlledReferenceThetaGeometry.carrier_observations_eq P P.coefficient haP Λ v b hvb
    Z htarget hstop F hF hFm a (0,(0,0)) k p
  unfold MixedPastMeanFirstMoment.value
  simp only [cappedAverage]
  have hpθ : (q:ℝ)≤(carrier (Base (θ,(U ω,Dir ω))) k).terminal (separated k (x,t,y)) := by
    change (q:ℝ)≤(carrier (Base a) k).terminal p
    rw [ht]
    exact hp.le
  simp only [ho,m,a,p,min_eq_left hpθ]

end SHE.MixedPastMeanFourier

