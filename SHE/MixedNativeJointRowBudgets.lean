module

public import SHE.MixedNativeJointFrozenRows
public import SHE.MixedNativeJointVarianceRows
public import SHE.NativeRowEnergyCast
public import SHE.FirstGammaCanonicalReferenceTime
public import SHE.NativeRowProductEnergy
public import SHE.ScalarHeatSixNorms
public import SHE.NativeJointGammaFields
public import SHE.MixedPastReferenceInput
public import SHE.FirstGammaCanonicalReferenceEnergy
public import SHE.ScalarHeatGradientOpenTime
public import SHE.ControlledVarianceGammaTime

@[expose] public section
noncomputable section

set_option autoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2300000

namespace SHE.MixedNativeJointRowBudgets
open MeasureTheory AddCircle GaussianIncrement NativeHeatObservation NativeObservationNaturality
open FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation PredictableL2
open scoped NNReal ENNReal
local instance firstGammaReferenceEnergy_period : Fact (0<2*Real.pi):=⟨by positivity⟩
local instance firstGammaFrozenValues_realSigma : MeasurableSpace RealL2 := borel _
local instance firstGammaFrozenValues_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance firstGammaFrozenValues_circleSigma : MeasurableSpace CircleL2 := borel _
local instance firstGammaFrozenValues_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩
local instance firstGammaFrozenValues_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance firstGammaFrozenValues_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance firstGammaFrozenValues_blockSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance firstGammaFrozenValues_blockBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
variable {Ω : Type*} [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
variable (Λ κ : ℝ) (hκ : 0<κ) {aU aV : ℝ→ℝ} (haU : Measurable aU) (haV : Measurable aV) {ell M : ℝ}
variable (hell : 0<ell) (hbU : ∀ z,ell≤aU z ∧ aU z≤M) (hbV : ∀ z,ell≤aV z ∧ aV z≤M)
variable (I₀ I₁ : StandardTerminalIto (C := RealHaarIntegrand.Columns) (E := RealL2) 𝓕 μ H)
variable (u₀ : RealL2)
variable (S : MixedNativeAdditiveResidualPair.Solution 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀)

variable (J:StandardTerminalIto (C:=Both RealHaarInput) (E:=ℝ) 𝓕 μ H)
variable (hIJ₀:StandardScalarNaturality I₀ (leftIntegral 𝓕 μ H J))
variable (hIJ₁:StandardScalarNaturality I₁ (rightIntegral 𝓕 μ H J))
variable (P:CanonicalCovariance.ProfileParameters) (hκP:κ<P.lower)
variable (hΛ:0≤Λ) (v b:ℝ≥0) (hvb:v<b) (hbH:b≤H) (hH:(H:ℝ)≤1)
variable (hwindow:(b:ℝ)-(v:ℝ)≤P.horizon)
variable (hsmall:ProfileStability.memoryConstant P.lower P.holder P.exponent*
  ProfileVolterra.powerConstant ((P.exponent-1)/4)*P.horizon^(P.exponent/4)≤1/2)
variable (Bpast:ℝ≥0) (hBDGpast:StandardTerminalBDGPower 2 J Bpast)
local notation "OldU"=>S.first v
local notation "OldD"=>(fun ω=>S.second v ω-S.first v ω)
local notation "OldUM"=>(((show IsStronglyPredictable 𝓕 S.first from S.first_predictable).stronglyAdapted v).measurable)
local notation "OldDM"=>((((show IsStronglyPredictable 𝓕 S.second from S.second_predictable).stronglyAdapted v).sub
  ((show IsStronglyPredictable 𝓕 S.first from S.first_predictable).stronglyAdapted v)).measurable)
local notation "Bbound"=>((show (b:ℝ)≤(H:ℝ) by exact_mod_cast hbH).trans hH)


local notation "UU"=>Function.uncurry S.first
local notation "VV"=>Function.uncurry S.second

local notation "Fields"=>MixedNativeJointRowFields.fields 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P hκP v b hbH hH
local notation "Grad"=>MixedNativeVarianceGammaTime.gradient 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P v b
local notation "Cur"=>MixedNativeVarianceGammaTime.currentMean 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S v b
local notation "Ref"=>MixedNativeVarianceGammaTime.referenceMean 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P hκP v b hbH hH

local notation "Rtime"=>FirstGammaCanonicalReferenceTime.reference_time 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P hκP v hH b hbH
local notation "Vtime"=>FirstGammaCanonicalReferenceTime.variance_time 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P v b

def timeBudget (a:ℝ→ℝ) (j:ℕ) (ρ:ℝ) (i l:Fin 6):ℝ≥0∞:=
  ∫⁻τ in Set.Ioc (0:ℝ) ((b:ℝ)-(v:ℝ)),∫⁻ω,
    ENNReal.ofReal (τ^(ρ-1/2)*‖NativeRandomRows.nativeRow (Fields a j i) (((b:ℝ)-τ).toNNReal,ω)-
      NativeRandomRows.nativeRow (Fields a j l) (((b:ℝ)-τ).toNNReal,ω)‖^2) ∂μ
local notation "Budget"=>timeBudget 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P hκP v b hbH hH

include hvb in
/-- Exact time/sample integral normalization of the actual native rows. -/
theorem timeBudget_cast {a:ℝ→ℝ} (ha:SmoothCylinders.BoundedSmooth a) {A ρ:ℝ} (hA:0≤A)
    (hholder:∀x y,|a x-a y|≤A*|x-y|^P.exponent)
    (hnull:NullCompleteFiltration.ContainsNullSets 𝓕 μ)
    (B0 B1:ℝ≥0) (hBDG0:StandardTerminalBDG16 I₀ B0) (hBDG1:StandardTerminalBDG16 I₁ B1)
    (j:ℕ) (i l:Fin 6)
    (hi:IntegrableOn (fun τ=>τ^(ρ-1/2)*(∫ω,‖NativeRandomRows.nativeRow (Fields a j i) (((b:ℝ)-τ).toNNReal,ω)-
      NativeRandomRows.nativeRow (Fields a j l) (((b:ℝ)-τ).toNNReal,ω)‖^2 ∂μ)) (Set.Ioc (0:ℝ) ((b:ℝ)-(v:ℝ)))):
    Budget a j ρ i l=ENNReal.ofReal (∫τ in Set.Ioc (0:ℝ) ((b:ℝ)-(v:ℝ)),τ^(ρ-1/2)*
      (∫ω,‖NativeRandomRows.nativeRow (Fields a j i) (((b:ℝ)-τ).toNNReal,ω)-
        NativeRandomRows.nativeRow (Fields a j l) (((b:ℝ)-τ).toNNReal,ω)‖^2 ∂μ)):=by
  have hm(n:Fin 6):Measurable (Fields a j n):=
    MixedNativeJointRowFields.fields_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P hκP
      v b hvb hbH hH hnull B0 B1 hBDG0 hBDG1 a ha j n
  have hb(n:Fin 6)(p:ℝ≥0×Ω)(x:HeatCircle):‖Fields a j n (p,x)‖≤ScalarHeatSingleMultiplier.cap A P.exponent j:=
    MixedNativeJointRowFields.fields_bound 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P hκP
      v b hbH hH ha hA hholder j n p x
  have hcap:0≤ScalarHeatSingleMultiplier.cap A P.exponent j:=by
    unfold ScalarHeatSingleMultiplier.cap
    have hc:=ScalarGaussianJetScale.constant_nonneg P.exponent 0
    have hr:=CompactMollifier.radius_pos (j+1)
    positivity
  exact NativeRowEnergyCast.time μ (Fields a j i) (Fields a j l) (hm i) (hm l) hcap (hb i) (hb l)
    (fun τ=>((b:ℝ)-τ).toNNReal) hi

include hIJ₀ hIJ₁ hΛ hH hvb hbH hwindow hsmall hBDGpast in
/-- The actual current variance slot in the positive-integral budget. -/
theorem current_variance {a:ℝ→ℝ} (ha:SmoothCylinders.BoundedSmooth a) {A ρ:ℝ}
    (hA:0≤A) (hρ0:-(1/2:ℝ)<ρ) (hρ1:ρ<1/2)
    (hholder:∀x y,|a x-a y|≤A*|x-y|^P.exponent)
    (hnull:NullCompleteFiltration.ContainsNullSets 𝓕 μ)
    (B0 B1:ℝ≥0) (hBDG0:StandardTerminalBDG16 I₀ B0) (hBDG1:StandardTerminalBDG16 I₁ B1) (j:ℕ):
    Budget a j ρ 1 2≤ENNReal.ofReal (MixedNativeVarianceGammaTime.constant P A ρ*
      (CompactMollifier.radius (j+1))^(2*P.exponent+4*ρ)*((b:ℝ)-(v:ℝ))^((P.exponent-1)/2)*
        (∫ω,‖S.second v ω-S.first v ω‖^2 ∂μ)):=by
  have he:=MixedNativeJointVarianceRows.current_energy (𝓕:=𝓕) (μ:=μ) (H:=H) (Λ:=Λ) (κ:=κ) (hκ:=hκ)
    (haU:=haU) (haV:=haV) (hell:=hell) (hbU:=hbU) (hbV:=hbV) (I₀:=I₀) (I₁:=I₁) (u₀:=u₀) (S:=S)
    (J:=J) (hIJ₀:=hIJ₀) (hIJ₁:=hIJ₁) (P:=P) (hκP:=hκP) (hΛ:=hΛ) (v:=v) (b:=b)
    (hvb:=hvb) (hbH:=hbH) (hH:=hH) (hwindow:=hwindow) (hsmall:=hsmall) (Bpast:=Bpast) (hBDGpast:=hBDGpast)
    ha hA hρ0 hρ1 hholder hnull B0 B1 hBDG0 hBDG1 j
  rw [timeBudget_cast 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P hκP v b hvb hbH hH
    ha hA hholder hnull B0 B1 hBDG0 hBDG1 j 1 2 he.1]
  exact ENNReal.ofReal_le_ofReal he.2

include hIJ₀ hIJ₁ hΛ hH hvb hbH hwindow hsmall hBDGpast in
/-- The actual frozen-reference variance slot in the positive budget. -/
theorem reference_variance {a:ℝ→ℝ} (ha:SmoothCylinders.BoundedSmooth a) {A ρ:ℝ}
    (hA:0≤A) (hρ0:-(1/2:ℝ)<ρ) (hρ1:ρ<1/2)
    (hholder:∀x y,|a x-a y|≤A*|x-y|^P.exponent)
    (hnull:NullCompleteFiltration.ContainsNullSets 𝓕 μ)
    (B0 B1:ℝ≥0) (hBDG0:StandardTerminalBDG16 I₀ B0) (hBDG1:StandardTerminalBDG16 I₁ B1) (j:ℕ):
    Budget a j ρ 4 5≤ENNReal.ofReal (MixedNativeVarianceGammaTime.constant P A ρ*
      (CompactMollifier.radius (j+1))^(2*P.exponent+4*ρ)*((b:ℝ)-(v:ℝ))^((P.exponent-1)/2)*
        (∫ω,‖S.second v ω-S.first v ω‖^2 ∂μ)):=by
  have he:=MixedNativeJointVarianceRows.reference_energy (𝓕:=𝓕) (μ:=μ) (H:=H) (Λ:=Λ) (κ:=κ) (hκ:=hκ)
    (haU:=haU) (haV:=haV) (hell:=hell) (hbU:=hbU) (hbV:=hbV) (I₀:=I₀) (I₁:=I₁) (u₀:=u₀) (S:=S)
    (J:=J) (hIJ₀:=hIJ₀) (hIJ₁:=hIJ₁) (P:=P) (hκP:=hκP) (hΛ:=hΛ) (v:=v) (b:=b)
    (hvb:=hvb) (hbH:=hbH) (hH:=hH) (hwindow:=hwindow) (hsmall:=hsmall) (Bpast:=Bpast) (hBDGpast:=hBDGpast)
    ha hA hρ0 hρ1 hholder hnull B0 B1 hBDG0 hBDG1 j
  rw [timeBudget_cast 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P hκP v b hvb hbH hH
    ha hA hholder hnull B0 B1 hBDG0 hBDG1 j 4 5 he.1]
  exact ENNReal.ofReal_le_ofReal he.2

variable (B:ℝ≥0) (hBDG:StandardTerminalBDG16 J B)
include hIJ₀ hIJ₁ hΛ hH hvb hbH hwindow hsmall hBDGpast hBDG in
/-- The actual compatible frozen-root positive budget, with the
original clipped past energy and no assumed joint reference versions. -/
theorem reference_root {a:ℝ→ℝ} (ha:SmoothCylinders.BoundedSmooth a) {A ρ:ℝ}
    (hA:0≤A) (hρ0:-(1/2:ℝ)<ρ) (hρ1:ρ<1/2)
    (hholder:∀x y,|a x-a y|≤A*|x-y|^P.exponent)
    (hnull:NullCompleteFiltration.ContainsNullSets 𝓕 μ)
    (B0 B1:ℝ≥0) (hBDG0:StandardTerminalBDG16 I₀ B0) (hBDG1:StandardTerminalBDG16 I₁ B1)
    (hlocal:StandardTerminalPastLocality I₁) (Bnext:ℝ≥0) (hBDGnext:StandardTerminalBDGPower 1 I₁ Bnext) (j:ℕ):
    Budget a j ρ 3 4≤ENNReal.ofReal ((2*A*ScalarHeatGradientDifference.constant P.exponent)^2*
      ScalarHeatBandTime.massConstant P.exponent ρ*(ProfileVariance.lowerConstant*P.lower)^(-1-2*ρ)*
        (CompactMollifier.radius (j+1))^(2*P.exponent+4*ρ)*
          min 1 ((2*((0-1:ℝ)^2+(Bnext:ℝ)*PastReferenceBracket.energyConstant P κ 0 1 1)*
            (∫ω,‖S.second v ω-S.first v ω‖^2 ∂μ))/(CompactMollifier.radius (j+1))^2)):=by
  have he:=MixedNativeJointFrozenRows.energy (𝓕:=𝓕) (μ:=μ) (H:=H) (Λ:=Λ) (κ:=κ) (hκ:=hκ)
    (haU:=haU) (haV:=haV) (hell:=hell) (hbU:=hbU) (hbV:=hbV) (I₀:=I₀) (I₁:=I₁) (u₀:=u₀) (S:=S)
    (J:=J) (hIJ₀:=hIJ₀) (hIJ₁:=hIJ₁) (P:=P) (hκP:=hκP) (hΛ:=hΛ) (v:=v) (b:=b)
    (hvb:=hvb) (hbH:=hbH) (hH:=hH) (hwindow:=hwindow) (hsmall:=hsmall) (Bpast:=Bpast) (hBDGpast:=hBDGpast)
    (B:=B) (hBDG:=hBDG) ha hA hρ0 hρ1 hholder hnull B0 B1 hBDG0 hBDG1 hlocal Bnext hBDGnext j
  dsimp only at he
  rw [timeBudget_cast 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P hκP v b hvb hbH hH
    ha hA hholder hnull B0 B1 hBDG0 hBDG1 j 3 4 he.1]
  exact ENNReal.ofReal_le_ofReal he.2
end SHE.MixedNativeJointRowBudgets
