module

public import SHE.MixedNativeJointGammaDensities
public import SHE.MixedNativeJointGammaSplitEnergy
public import SHE.NativeJointGammaAgeSplit
public import SHE.NativeGammaAgeNormalize
public import SHE.MixedNativeJointRowBudgets
public import SHE.MixedNativeFrozenFactorPositive
public import SHE.MixedNativeSignedGammaRows
public import SHE.GammaBandConstants
public import SHE.NativeGammaAgeBound
public import SHE.MixedNativeGammaEnergy
public import SHE.FirstGammaCanonicalReference
public import SHE.FirstGammaEndpointPhysical
public import SHE.MixedNativeFrozenPrefixIto
public import SHE.FirstGammaAffine
public import SHE.FirstGammaRows
public import SHE.FirstGammaConstruction
public import SHE.FirstGammaValues
public import SHE.FiniteReferenceSpliceRows
public import SHE.MixedNativeFrozenInterpolationRows
public import SHE.MixedNativeFrozenPrefixValues
public import SHE.FiniteReferenceSplicePast
public import SHE.StoppedInputAlgebra
public import SHE.PastFrozenPrefixRows
public import SHE.MixedPastJointData
public import SHE.FiniteReferenceSplice
public import SHE.MixedNativeJointPhysical
public import SHE.MixedNativePairMartingale
public import SHE.MixedNativeJointObservation
public import SHE.NativeJointPhysicalRows
public import SHE.NativeJointBracketDefect
public import SHE.NativeJointCovariance
public import SHE.NativeJointPhysicalStep

@[expose] public section
noncomputable section

set_option autoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 2300000

namespace SHE.MixedNativeJointGammaBudget
open MeasureTheory GaussianIncrement NativeHeatObservation NativeObservationNaturality
open FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation PredictableL2
open scoped NNReal ENNReal
local instance mixedNativeJointGammaAgeEnergy_realSigma : MeasurableSpace RealL2 := borel _
local instance mixedNativeJointGammaAgeEnergy_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance mixedNativeJointGammaAgeEnergy_circleSigma : MeasurableSpace CircleL2 := borel _
local instance mixedNativeJointGammaAgeEnergy_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩
local instance mixedNativeJointGammaAgeEnergy_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance mixedNativeJointGammaAgeEnergy_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance mixedNativeJointGammaAgeEnergy_blockSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance mixedNativeJointGammaAgeEnergy_blockBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
local instance mixedNativeJointGammaAgeEnergy_period : Fact (0<2*Real.pi):=⟨by positivity⟩
local instance mixedNativeJointGammaAgeEnergy_unitSigma : MeasurableSpace CircleHeat.CircleL2:=borel _
local instance mixedNativeJointGammaAgeEnergy_unitBorel : BorelSpace CircleHeat.CircleL2:=⟨rfl⟩
variable {Ω : Type} [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
variable (Λ κ : ℝ) (hκ : 0<κ) {aU aV : ℝ→ℝ} (haU : Measurable aU) (haV : Measurable aV) {ell M : ℝ}
variable (hell : 0<ell) (hbU : ∀ z,ell≤aU z ∧ aU z≤M) (hbV : ∀ z,ell≤aV z ∧ aV z≤M)
variable (I₀ I₁ : StandardTerminalIto (C := RealHaarIntegrand.Columns) (E := RealL2) 𝓕 μ H)
variable (u₀ : RealL2)
variable (S : MixedNativeAdditiveResidualPair.Solution 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀)

variable (P : CanonicalCovariance.ProfileParameters) (hκP : κ<P.lower)
variable (v b : ℝ≥0) (hbH : b≤H) (hb1 : (b:ℝ)≤1) (hb0 : 0<b)
variable (hnull : NullCompleteFiltration.ContainsNullSets 𝓕 μ)
variable (B0 B1 : ℝ≥0) (hBDG0 : StandardTerminalBDG16 I₀ B0) (hBDG1 : StandardTerminalBDG16 I₁ B1)
variable (J : StandardTerminalIto (C:=Both RealHaarInput) (E:=ℝ) 𝓕 μ H)
variable {a : ℝ→ℝ} (ha : SmoothCylinders.BoundedSmooth a) {A β : ℝ}
variable (hA : 0≤A) (hβ : 0≤β) (hβ1 : β≤1) (hh : ∀x y,|a x-a y|≤A*|x-y|^β) (j : ℕ)
variable (hΛ : 1≤Λ) {ρ : ℝ} (hρ : 0<ρ) (hρhalf : ρ<1/2)

variable (hH:(H:ℝ)≤1)
open Set MixedNativeGammaEnergy
local notation "Lower"=>commonLower (ell:=ell) (P:=P) (κ:=κ)
local notation "Upper"=>commonUpper (M:=M) (P:=P) (κ:=κ)
local notation "hm"=>commonLower_pos (ell:=ell) (P:=P) (κ:=κ) (hell:=hell) (hκP:=hκP)
local notation "cU"=>currentFirst 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S P
local notation "cV"=>currentSecond 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S P
local notation "Trace"=>NativeConvexGammaUniform.constant Lower Upper hm hρ hρhalf
local notation "Higher"=>HaarWeightedHeat.higherConstant Lower Upper hm 0 ρ
local notation "Signed"=>NativeJointGammaAgeSplit.signed (v:=v) (b:=b) (P:=P) (A:=A) (β:=P.exponent) (j:=j) hΛ hρ hρhalf hm cU cV
local notation "Frozen"=>NativeJointGammaAgeSplit.frozen (v:=v) (b:=b) (U:=Function.uncurry S.first) (V:=Function.uncurry S.second)
  (P:=P) (Λ:=Λ) (κ:=κ) (hκP:=hκP) (m:=Lower) (W:=Upper) (hmP:=min_le_right _ _) (hWP:=le_max_right _ _)
  (A:=A) (β:=P.exponent) (j:=j) (ρ:=ρ) hm
local notation "Rslot"=>NativeJointGammaAgeSplit.row (𝓕:=𝓕) (μ:=μ) (H:=H) (v:=v) (b:=b) (hbH:=hbH) (hb1:=hb1)
  (U:=Function.uncurry S.first) (V:=Function.uncurry S.second) (hU:=S.first_predictable) (hV:=S.second_predictable)
  (P:=P) (Λ:=Λ) (κ:=κ) (hκ:=hκ) (hκP:=hκP) (I0:=I₀) (I1:=I₁) (a:=a) (ρ:=ρ) j
local notation "OldSigned"=>MixedNativeSignedGammaRows.sectionEnergy 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P hΛ hρ.le A j v b
local notation "OldFrozen"=>MixedNativeFrozenFactorPositive.density 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P hκP v b A ρ j
local notation "Budget"=>MixedNativeJointRowBudgets.timeBudget 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P hκP v b hbH hH a j ρ

variable (hholder:∀x y,|a x-a y|≤A*|x-y|^P.exponent)
local notation "Ksum"=>(κ+Upper)*(1+2*HeatTrace.fractionalGaussianIntegral ρ)

include hb0 hnull B0 B1 hBDG0 hBDG1 J ha hA hΛ hρ hρhalf hholder in
/-- Complete ORIGINAL-J joint Gamma on the actual coupled solution,
normalized to the SAME six literal positive budgets whose sharp caps
are proved. No joint choice over past times or novel cap is assumed. -/
def actual_complete_energy :=
  let Cbudget:ℝ≥0∞:=6*(ENNReal.ofReal Trace*(∫⁻τ in Set.Ioc (0:ℝ) ((b:ℝ)-(v:ℝ)),OldSigned τ)+
    ENNReal.ofReal Higher*(∫⁻τ in Set.Ioc (0:ℝ) ((b:ℝ)-(v:ℝ)),∫⁻ω,ENNReal.ofReal (OldFrozen τ ω) ∂μ)+
    ENNReal.ofReal Ksum*(Budget 0 1+Budget 1 2+Budget 3 4+Budget 4 5))
  (MixedNativeJointGammaSplitEnergy.actual_complete_energy
        (𝓕:=𝓕) (μ:=μ) (H:=H) (Λ:=Λ) (κ:=κ) (hκ:=hκ) (haU:=haU)
        (haV:=haV) (hell:=hell) (hbU:=hbU) (hbV:=hbV) (I₀:=I₀) (I₁:=I₁) (u₀:=u₀)
        (S:=S) (P:=P) (hκP:=hκP) (v:=v) (b:=b) (hbH:=hbH) (hb1:=hb1)
        (hb0:=hb0) (hnull:=hnull) (B0:=B0) (B1:=B1) (hBDG0:=hBDG0) (hBDG1:=hBDG1) (J:=J)
        (ha:=ha) (hA:=hA) (j:=j) (hΛ:=hΛ) (ρ:=ρ) (hρ:=hρ) (hρhalf:=hρhalf)
        (v₀:=u₀) (hβ:=P.exponent_pos.le) (hβ1:=P.exponent_le_one) (hh:=hholder)).trans (c:=Cbudget) (by
    have hs:(∫⁻τ in Set.Ioc (0:ℝ) ((b:ℝ)-(v:ℝ)),∫⁻ω,ENNReal.ofReal (Signed (τ,ω)) ∂μ)=
        ENNReal.ofReal Trace*(∫⁻τ in Set.Ioc (0:ℝ) ((b:ℝ)-(v:ℝ)),OldSigned τ):=by
      calc
        _=(∫⁻τ in Set.Ioc (0:ℝ) ((b:ℝ)-(v:ℝ)),ENNReal.ofReal Trace*OldSigned τ):=by
          apply lintegral_congr
          intro τ
          exact MixedNativeJointGammaDensities.signed_section
            (𝓕:=𝓕) (μ:=μ) (H:=H) (Λ:=Λ) (κ:=κ) (hκ:=hκ) (haU:=haU)
            (haV:=haV) (hell:=hell) (hbU:=hbU) (hbV:=hbV) (I₀:=I₀) (I₁:=I₁) (u₀:=u₀)
            (S:=S) (P:=P) (hκP:=hκP) (v:=v) (b:=b) (A:=A) (j:=j)
            (ρ:=ρ) (hΛ:=hΛ) (hρ:=hρ) (hρhalf:=hρhalf) τ
        _=_:=lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    have hf:=MixedNativeJointGammaDensities.frozen_mass
        (𝓕:=𝓕) (μ:=μ) (H:=H) (Λ:=Λ) (κ:=κ) (hκ:=hκ) (haU:=haU)
        (haV:=haV) (hell:=hell) (hbU:=hbU) (hbV:=hbV) (I₀:=I₀) (I₁:=I₁) (u₀:=u₀)
        (S:=S) (P:=P) (hκP:=hκP) (v:=v) (b:=b) (A:=A) (j:=j)
        (ρ:=ρ) (hρ:=hρ) (hρhalf:=hρhalf)
    have hr(i l:Fin 6):=(MixedNativeJointGammaDensities.row_mass
        (𝓕:=𝓕) (μ:=μ) (H:=H) (Λ:=Λ) (κ:=κ) (hκ:=hκ) (haU:=haU)
        (haV:=haV) (hell:=hell) (hbU:=hbU) (hbV:=hbV) (I₀:=I₀) (I₁:=I₁) (u₀:=u₀)
        (S:=S) (P:=P) (hκP:=hκP) (v:=v) (b:=b) (hbH:=hbH) (hb1:=hb1)
        (hH:=hH) (a:=a) (j:=j) (ρ:=ρ) i l)
    change 6*((∫⁻τ in Ioc (0:ℝ) ((b:ℝ)-(v:ℝ)),∫⁻ω,ENNReal.ofReal (Signed (τ,ω)) ∂μ)+
      (∫⁻τ in Ioc (0:ℝ) ((b:ℝ)-(v:ℝ)),∫⁻ω,ENNReal.ofReal (Frozen (τ,ω)) ∂μ)+
      ENNReal.ofReal Ksum*((∫⁻τ in Ioc (0:ℝ) ((b:ℝ)-(v:ℝ)),∫⁻ω,ENNReal.ofReal (Rslot 0 1 (τ,ω)) ∂μ)+
        (∫⁻τ in Ioc (0:ℝ) ((b:ℝ)-(v:ℝ)),∫⁻ω,ENNReal.ofReal (Rslot 1 2 (τ,ω)) ∂μ)+
        (∫⁻τ in Ioc (0:ℝ) ((b:ℝ)-(v:ℝ)),∫⁻ω,ENNReal.ofReal (Rslot 3 4 (τ,ω)) ∂μ)+
        (∫⁻τ in Ioc (0:ℝ) ((b:ℝ)-(v:ℝ)),∫⁻ω,ENNReal.ofReal (Rslot 4 5 (τ,ω)) ∂μ)))≤Cbudget
    rw [hs,hf,hr 0 1,hr 1 2,hr 3 4,hr 4 5])
end SHE.MixedNativeJointGammaBudget
