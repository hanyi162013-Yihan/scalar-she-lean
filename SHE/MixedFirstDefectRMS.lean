module

public import SHE.MixedCanonicalRootFields
public import SHE.DefectRelativeFactor
public import SHE.DefectCombinedTime
public import SHE.NativeBesselFieldAE
public import SHE.NativeSignedHaarProcess
public import SHE.ControlledScalarReference
public import SHE.ControlledThetaDefectEnvelope
public import SHE.MixedJointUncutDefectTrace

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

namespace SHE.MixedFirstDefectRMS
open Set MeasureTheory Real AddCircle StoppedFourier OrthogonalItoChannels DyadicApproximation PredictableL2
  NativeHeatObservation CutoffWordLevel CutoffWordHistories CutoffCarriers ControlledProfile
  ControlledReferenceLevel PhysicalChainArrays PhysicalParentGeometry PhysicalScoreChain HistoryProductMeasure
  CoveredControlledLaw
open scoped NNReal ENNReal BigOperators
open Classical
local instance mixedFirstDefectRMS_period:Fact (0<2*π):=⟨by positivity⟩
local instance mixedFirstDefectRMS_unit:Fact (0<(1:ℝ)):=⟨zero_lt_one⟩
local instance mixedFirstDefectRMS_sigma:MeasurableSpace CircleL2:=borel _
local instance mixedFirstDefectRMS_borel:BorelSpace CircleL2:=⟨rfl⟩
variable {Ω:Type}[MeasurableSpace Ω]
variable (𝓕:Filtration ℝ≥0 ‹MeasurableSpace Ω›)(μ:Measure Ω)[IsProbabilityMeasure μ](H:ℝ≥0)
variable (Λ κ:ℝ)(hκ:0<κ){aU aV:ℝ→ℝ}(haU:Measurable aU)(haV:Measurable aV){ell M:ℝ}
variable (hell:0<ell)(hbU:∀z,ell≤aU z ∧ aU z≤M)(hbV:∀z,ell≤aV z ∧ aV z≤M)
variable (I₀ I₁:StandardTerminalIto (C:=RealHaarIntegrand.Columns) (E:=RealL2) 𝓕 μ H)
variable (u₀ v₀:RealL2)
variable (S:MixedNativeAdditiveResidualPair.Solution 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀)
variable (P:CanonicalCovariance.ProfileParameters)(hAs:SmoothCylinders.BoundedSmooth (fun z=>κ+aV z))
variable (θ:ℝ)(v b:ℝ≥0)(hvb:v≤b)
variable (F:HeatCircle→WordRecursion.State 1→ℝ)(hF:UniformSmooth.UniformBoundedSmooth F)
variable (hFm:Measurable (fun z:HeatCircle×WordRecursion.State 1=>F z.1 z.2))
local notation "Z"=>ControlledScalarReference.observations b
local notation "Base"=>ControlledReferenceThetaGeometry.level P (fun z=>κ+aV z) hAs Λ v b hvb Z
  (fun _ _=>le_rfl) (fun _ _=>le_rfl) F hF hFm
local notation "Zero"=>Base (0,(0,0))
local notation "R₀"=>referenceData P (fun z=>κ+aV z) hAs Λ 0 v b hvb (0,0)

/-- The literal root-retained full first-defect field in the actual
random-past finite expansion. Both cross terms and the quadratic term
remain inside MixedJointUncutMark. -/
def field (k:ℕ):Ω×HeatCircle→ℝ:=
  MixedCanonicalRootFields.field 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
    P hAs θ v b hvb Z (fun _ _=>le_rfl) (fun _ _=>le_rfl) F hF hFm 2 k

def value (ρ:ℝ)(hΛ:1≤Λ)(hρ:0≤ρ)(k:ℕ)(ω:Ω):CircleL2:=
  NativeBesselFieldAE.value Λ ρ hΛ hρ
    (fun z:Ω×HeatCircle=>(field 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
      P hAs θ v b hvb F hF hFm k z:ℂ)) ω

def inputEnergy (ρ:ℝ)(hΛ:1≤Λ)(hρ:0≤ρ)(q:ℝ)(ω:Ω):ℝ:=
  NativeSignedHaarProcess.inputEnergy hΛ hρ
    (ContinuousHeatMild.coefficientFunction haU hell hbU S.first (q.toNNReal,ω))
    (ContinuousHeatMild.coefficientFunction haV hell hbV S.second (q.toNNReal,ω))

/-- Original law/current time q, actual random past data and the full
joint covariance defect, BEFORE its time integral. -/
def point (k:ℕ)(h:History HeatCircle k)(ω:Ω)(q:ℝ):ℝ:=
  MixedJointUncutDefectTrace.activePoint 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
    (Base (θ,MixedNativeRandomReferenceStep.randomParameter
      𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S v ω)) k ((h,ω),q)

def spatialPoint (k:ℕ)(t:Fin k→ℝ)(q:ℝ)(ω:Ω)(x:HeatCircle):ℝ:=
  ∫w:Fin k→HeatCircle,point 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
    P hAs θ v b hvb F hF hFm k (separated k (x,t,w)) ω q
    ∂Measure.pi (fun _=>haarAddCircle)

def pointValue (ρ:ℝ)(hΛ:1≤Λ)(hρ:0≤ρ)(k:ℕ)(t:Fin k→ℝ)(q:ℝ)(ω:Ω):CircleL2:=
  NativeBesselFieldAE.value Λ ρ hΛ hρ
    (fun z:Ω×HeatCircle=>(spatialPoint 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
      P hAs θ v b hvb F hF hFm k t q z.1 z.2:ℂ)) ω

/-- This is the exact deterministic all-original-pair new-time kernel;
there is no selected or contracted observation law in the definition. -/
def pairKernel (ρ:ℝ)(k:ℕ)(t:Fin k→ℝ)(q:ℝ):ℝ:=
  let z:=separated k ((0:HeatCircle),t,fun _=>0)
  let T:=(carrier Zero k).terminal z
  ∑i:Fin (1+k),∑j:Fin (1+k),DefectCombinedTime.kernel Λ ρ
    (targets Zero k z i-T) (targets Zero k z j-T) (T-q)

def oldFactor (k:ℕ)(t:Fin k→ℝ)(A0 ν:ℝ):ℝ:=
  let z:=separated k ((0:HeatCircle),t,fun _=>0)
  timeWeight Zero (ControlledOldIntervals.fraction P*P.lower)
    (uniformConstant 1) k z*
      DefectRelativeFactor.total Zero P v k z A0 ν

/-- The required RMS convolution keeps the actual current negative
input INSIDE the new-time integral, before squaring. Old histories use
their original finite Lebesgue product, with the full strict-order mask. -/
def convolution (ρ:ℝ)(hΛ:1≤Λ)(hρ:0≤ρ)(k:ℕ)(A0 ν:ℝ)(ω:Ω):ℝ:=
  ∫t:Fin k→ℝ,
    let z:=separated k ((0:HeatCircle),t,fun _=>0)
    if StrictHistory Zero k z then
      oldFactor Λ κ P hAs v b hvb F hF hFm k t A0 ν*
        (∫q:ℝ,pairKernel Λ κ P hAs v b hvb F hF hFm ρ k t q*
          sqrt (inputEnergy 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S ρ hΛ hρ q ω)
          ∂volume.restrict (Ioc (v:ℝ) ((carrier Zero k).terminal z)))
    else 0
    ∂Measure.pi (fun _:Fin k=>volume.restrict (Ioc (v:ℝ) b))

end SHE.MixedFirstDefectRMS
