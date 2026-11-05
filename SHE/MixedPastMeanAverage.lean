module

public import SHE.MixedPastSpatialMoments
public import SHE.ControlledFamilyMeanFields
public import SHE.MixedPastKernelSections
public import SHE.ControlledFamilyMeanEnergy
public import SHE.MixedPastMeanInputEnergy
public import SHE.NativeKernelReindex
public import SHE.MixedPastMeanFields
public import SHE.MixedPastMeanSupport
public import SHE.PastMeanRMS
public import SHE.PastMeanDampedTime
public import SHE.HilbertFiniteAverage
public import SHE.PastMeanMinkowski

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 450000
set_option quotPrecheck false

namespace SHE.MixedPastMeanAverage
open MeasureTheory PredictableL2 NativeHeatObservation NativeObservationNaturality
  FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation StoppedItoInputs
open scoped NNReal ENNReal
local instance mixedPastMeanAverage_realSigma : MeasurableSpace RealL2 := borel _
local instance mixedPastMeanAverage_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance mixedPastMeanAverage_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance mixedPastMeanAverage_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance mixedPastMeanAverage_blockSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance mixedPastMeanAverage_blockBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
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
local instance mixedPastMeanAverage_circleSigma : MeasurableSpace CircleL2 := borel _
local instance mixedPastMeanAverage_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩
local instance mixedPastMeanAverage_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
local instance mixedPastMeanAverage_secondCountable : SecondCountableTopology CircleL2 :=
  (_root_.fourierBasis (T:=2*Real.pi)).repr.toHomeomorph.secondCountableTopology
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
local notation "Input" => MixedPastMeanInputEnergy.input 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP v b hvb Z htarget hstop F hF hFm
attribute [local irreducible] MixedPastLiteralPoint.meanField MixedPastJointData.pastU MixedPastJointData.pastD
attribute [local irreducible] MixedPastMeanInputEnergy.input

include hIJ₀ hIJ₁ in
/-- The actual correlated random-past mean input is averaged over the
original old-time cube before squaring. Its exact relative-age budget
retains every root clip and rough-block minimum gap, including depth zero. -/
theorem actual_averaged_energy (hlocal : StandardTerminalPastLocality J) (hΛ : 0<Λ)
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
    (ε : ℝ) (hε : 0≤ε) (hεhalf : ε<1/2)
    (q : ℝ≥0) (hvq : v≤q) (hqb : q<b) (hqH : q≤H) (hq1 : (q:ℝ)≤1) :
    let N:=(2*p)*(k+2)
    let CG:=MixedPastWordMoments.momentConstant P k k (2*p)
      ((k:ℝ)*(NativeHybridMoments.momentConstant N B0 κ M)^P.exponent)
    let CD:=MixedHeatedDifferenceMoments.momentConstant N B0 κ M^((1-χ)/(k+2:ℝ))
    let C:=((CD+CG)/2)^(1/(p:ℝ))
    let K:=PastMeanRMS.coefficient P k ρ C*((b:ℝ)-q)^(ρ/2)
    let E:=∫ ω,‖S.second q ω-S.first q ω‖^2 ∂μ
    let old:=Measure.pi (fun _ : Fin k=>volume.restrict (Ioc (v:ℝ) (b:ℝ)))
    let raw : (Fin k→ℝ)×Ω→CircleL2:=fun z=>Input k θ q mass ρ hmass hρ.le z.1 z.2
    Integrable raw (old.prod μ) ∧
      Integrable (fun ω=>‖∫ t,raw (t,ω) ∂old‖^2) μ ∧
      (∫ ω,‖∫ t,raw (t,ω) ∂old‖^2 ∂μ)≤
        (K*E^(χ/2)*((4:ℝ)^ε*Λ^(-ε))*
          QuarterRMSTimeFactors.oldTimeBudget P (fraction P*P.lower) (uniformConstant 1)
            k ((b:ℝ)-v) ((q:ℝ)-v) (1/2-ε) A0 ν)^2 := by
  intro N CG CD C K E old raw
  have hE : 0≤E:=integral_nonneg (fun _=>sq_nonneg _)
  have hCD : 0≤CD:=rpow_nonneg
    (MixedHeatedDifferenceMoments.momentConstant_nonneg (κ:=κ) hκ.le
      (hell.le.trans ((hbU 0).1.trans (hbU 0).2)) N B0) _
  have hCG : 0≤CG:=MixedPastWordMoments.momentConstant_nonneg P k k (2*p) _
  have hC : 0≤C:=rpow_nonneg (div_nonneg (add_nonneg hCD hCG) (by norm_num)) _
  have hraw0:=MixedPastMeanFields.input_joint_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
    P haP v b hvb Z htarget hstop F hF hFm hΛ.le k q mass ρ hmass hρ.le
  have hmap : Measurable (fun z : (Fin k→ℝ)×Ω=>(θ,z)):=measurable_const.prodMk measurable_id
  have hraw : Measurable raw:=hraw0.comp hmap
  have hs:=MixedPastMeanInputEnergy.actual_input_energy 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
    J hIJ₀ hIJ₁ P haP v b hvb Z htarget hstop F hF hFm hlocal hΛ.le hages hrootStop hrootTarget hcenter
    hspan k hfresh hold θ hθ A0 ν hA0 hν hjet χ hχ0 hχ1 p hp horder B0 hBDG mass ρ hmass hρ hρhalf q hvq hqH hq1
  have hz (t : Fin k→ℝ) (ha : ¬active Zero (b:ℝ) k q t) (ω : Ω) : raw (t,ω)=0:=
    MixedPastMeanSupport.input_zero_of_not_active
      𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP v b hvb Z htarget hstop F hF hFm
      k θ q mass ρ hmass hρ.le t ha ω
  have hh:=PastMeanRMS.old_time_energy Zero μ P (b:ℝ) (fun _=>rfl) k Λ q A0 ν ρ C E χ ε
    hΛ (by exact_mod_cast hvq) (by exact_mod_cast hqb) le_rfl hA0 hν hρ.le hρhalf hC hE hε hεhalf
    raw hraw hs hz
  exact hh

end SHE.MixedPastMeanAverage
