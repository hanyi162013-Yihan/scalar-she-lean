module

public import SHE.MixedPastSpatialMoments
public import SHE.ControlledFamilyMeanFields
public import SHE.MixedPastKernelSections
public import SHE.ControlledFamilyMeanEnergy

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3600000
set_option quotPrecheck false

namespace SHE.MixedPastMeanInputEnergy
open MeasureTheory PredictableL2 NativeHeatObservation NativeObservationNaturality
  FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation StoppedItoInputs
open scoped NNReal ENNReal
local instance mixedPastMeanInputEnergy_realSigma : MeasurableSpace RealL2 := borel _
local instance mixedPastMeanInputEnergy_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance mixedPastMeanInputEnergy_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance mixedPastMeanInputEnergy_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance mixedPastMeanInputEnergy_blockSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance mixedPastMeanInputEnergy_blockBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
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
local instance mixedPastMeanInputEnergy_circleSigma : MeasurableSpace CircleL2 := borel _
local instance mixedPastMeanInputEnergy_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩
local instance mixedPastMeanInputEnergy_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
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

/-- The entire native negative-output mean mark, applied to the actual
dependent current difference of the original mixed common-driver pair. -/
def input (k : ℕ) (θ : ℝ) (q : ℝ≥0) (mass ρ : ℝ) (hmass : 1≤mass) (hρ : 0≤ρ)
    (t : Fin k→ℝ) (ω : Ω) : CircleL2 :=
  OneInputOperator.besselHalf mass ρ hmass hρ
    (integralOperator (MixedPastKernelFields.spatial 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S
      P haP v b hvb Z htarget hstop F hF hFm k θ q q t) ω
      (embed (S.second q ω-S.first q ω)))

include hIJ₀ hIJ₁ in
/-- Actual correlated random-past mean input energy at every finite
word depth. All Gaussian, profile-family, spatial, relative-moment,
right-heat, current input and integrability premises are discharged.
The quantitative small factor is the ORIGINAL current L² energy, and
the exact time amplitude retains relative ages and quarter-row decay. -/
theorem actual_input_energy (hlocal : StandardTerminalPastLocality J) (hΛ : 0≤Λ)
    (hages : ∀ x i,(Z.observations x i).stop≤(Z.observations x i).target)
    (hrootStop : ∀ x i,(Z.observations x i).stop≤(b:ℝ))
    (hrootTarget : ∀ x i,(Z.observations x i).target=(b:ℝ))
    (hcenter : ∀ x,(Z.observations x 0).center=x)
    (hspan : (b:ℝ)-(v:ℝ)≤P.horizon) (k : ℕ)
    (hfresh : (b:ℝ)-(v:ℝ)≤UniformFutureProfileScores.horizon (1+k))
    (hold : ∀ j,j<k→(b:ℝ)-(v:ℝ)≤uniformHorizon 1 j)
    (θ : ℝ) (hθ : |θ|≤1) (A0 ν : ℝ) (hA0 : 0≤A0) (hν : 0≤ν)
    (hjet : ∀ x j,j≤k→∀ z,‖iteratedFDeriv ℝ j (F x) z‖≤A0*ν^j)
    (χ : ℝ) (hχ0 : 0≤χ) (hχ1 : χ<1) (p : ℕ) (hp : 0<p) (horder : 1≤(p:ℝ)*(1-χ))
    (B0 : ℝ≥0) (hBDG : StandardTerminalBDGPower ((2*p)*(k+2)) J B0)
    (mass ρ : ℝ) (hmass : 1≤mass) (hρ : 0<ρ) (hρhalf : ρ<1/2)
    (q : ℝ≥0) (hvq : v≤q) (hqH : q≤H) (hq1 : (q:ℝ)≤1) :
    let N:=(2*p)*(k+2)
    let CG:=MixedPastWordMoments.momentConstant P k k (2*p)
      ((k:ℝ)*(NativeHybridMoments.momentConstant N B0 κ M)^P.exponent)
    let CD:=MixedHeatedDifferenceMoments.momentConstant N B0 κ M^((1-χ)/(k+2:ℝ))
    ∀ᵐ t : Fin k→ℝ ∂Measure.pi (fun _=>volume.restrict (Ioc (v:ℝ) (b:ℝ))),
      active Zero (b:ℝ) k q t →
        let w:=PastMeanEnvelope.width (R:=Ref (0,(0,0))) (b:ℝ) k q t
        let amp:=PastMeanEnvelope.amplitude Zero P (b:ℝ) k Λ q A0 ν t
        let C:=GaussianNegativePacket.constant ρ*(NativeHeatSpan.clock w)^(ρ-1/2)*amp^2*
          ((CD+CG)/2)^(1/(p:ℝ))
        Integrable (fun ω=>‖input 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
          P haP v b hvb Z htarget hstop F hF hFm k θ q mass ρ hmass hρ.le t ω‖^2) μ ∧
          (∫ ω,‖input 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
            P haP v b hvb Z htarget hstop F hF hFm k θ q mass ρ hmass hρ.le t ω‖^2 ∂μ)≤
            C*(∫ ω,‖S.second q ω-S.first q ω‖^2 ∂μ)^χ := by
  intro N CG CD
  have hMom:=MixedPastKernelSections.normalized_quarter_moment 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S
    J hIJ₀ hIJ₁ P haP v b hvb Z htarget hstop F hF hFm hlocal hΛ hages hrootStop hrootTarget hcenter
    hspan k hfresh hold θ hθ A0 ν hA0 hν hjet (2*p) (by omega) B0 hBDG q hvq hqH
  let a : Ω→ℝ×Inputs:=fun ω=>(θ,(U ω,Dir ω))
  let m:=Mean k θ q
  have hU := (MixedPastJointData.pastU_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S v).mono (𝓕.le v) le_rfl
  have hD := (MixedPastJointData.pastD_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S v).mono (𝓕.le v) le_rfl
  have ha : Measurable a:=measurable_const.prodMk (hU.prodMk hD)
  have hm : Measurable (fun z : Ω×History HeatCircle k=>m z.1 z.2):=
    MixedPastLiteralFields.meanField_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S
      P haP v b hvb Z htarget hstop F hF hFm k θ q
  have hCG : 0≤CG:=MixedPastWordMoments.momentConstant_nonneg P k k (2*p) _
  filter_upwards [hMom] with t ht
  intro hactive w amp C
  let r:=quarterRowTime (R:=Ref (0,(0,0))) (b:ℝ) k q t
  obtain ⟨_,hqr,hrt,_,_,_⟩:=quarter_geometry (R:=Ref (0,(0,0))) (b:ℝ) k q t hactive.2
  have hfixed (a : ℝ×Inputs) : fixedTerminal (R:=Ref a) (b:ℝ) k t=
      fixedTerminal (R:=Ref (0,(0,0))) (b:ℝ) k t := by
    have hh:=ControlledReferenceThetaGeometry.carrier_terminal_eq P P.coefficient haP Λ v b hvb Z htarget hstop F hF hFm
      a (0,(0,0)) k (anchor k t)
    have ha:=terminal_separated (Base a) (b:ℝ) (fun _=>rfl) k t (0:HeatCircle) (fun _=>0)
    have hz:=terminal_separated Zero (b:ℝ) (fun _=>rfl) k t (0:HeatCircle) (fun _=>0)
    exact ha.symm.trans (hh.trans hz)
  have hr : ∀ a : ℝ×Inputs,r<fixedTerminal (R:=Ref a) (b:ℝ) k t := fun a=>by rw [hfixed a];exact hrt
  have hw : 0<w:=PastMeanEnvelope.width_pos Zero (b:ℝ) (fun _=>rfl) k q t hactive.2
  have hw1 : w≤1 := by
    change (b:ℝ)-r≤1
    have hvr : (v:ℝ)≤r := (show (v:ℝ)≤(q:ℝ) from by exact_mod_cast hvq).trans hqr.le
    linarith [P.horizon_le_one]
  have hamp : 0≤amp:=PastMeanEnvelope.amplitude_nonneg Zero P (b:ℝ) (fun _=>rfl) k Λ q A0 ν t hactive.2
  have hrel : ∀ᵐ z : Space ∂(haarAddCircle (T:=2*Real.pi)).prod haarAddCircle,
      (∫ ω,‖familyWeightedField Ref Base a k (fun _=>Λ) (fun _=>(q:ℝ)) (fun _=>r) m (fun _=>t) (ω,z)‖^(4*p) ∂μ)≤
        CG*(amp*‖ProfileVariance.heatPhysical (8*w) z.1 z.2‖)^(4*p) := by
    have he : 2*(2*p)=4*p:=by omega
    simpa only [MixedPastKernelFields.timeMoment,MixedPastKernelFields.quarterField,MixedPastKernelFields.timeField,
      MixedPastKernelFields.spatial,PastMeanEnvelope.envelope,he,CG,N,r,w,amp,a,m,familyWeightedField] using ht hactive
  have hh:=ControlledFamilyMeanEnergy.actual_input_energy 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
    J hIJ₀ hIJ₁ P P.coefficient haP v b hvb Z htarget hstop F hF hFm hΛ q hqH hq1 a ha k p hp m hm t r hqr.le hr
    B0 hBDG hmass hρ hρhalf hw hw1 hamp hχ0 hχ1 hCG horder hrel
  have hk : familyWeightedField Ref Base a k (fun _=>Λ) (fun _=>(q:ℝ)) (fun _=>(q:ℝ)) m (fun _=>t)=
      MixedPastKernelFields.spatial 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S
        P haP v b hvb Z htarget hstop F hF hFm k θ q q t := by
    funext z
    rfl
  dsimp only at hh
  simp only [familyMeanInput] at hh
  rw [hk] at hh
  simpa only [input,CD,N,C] using hh

end SHE.MixedPastMeanInputEnergy
