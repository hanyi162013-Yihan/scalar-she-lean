module

public import SHE.NativeCanonicalGammaSharp

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2500000
namespace SHE.NativeCanonicalGammaEnergy
open Set MeasureTheory PredictableL2 NativeHeatObservation DyadicApproximation StoppedFourier SmoothCylinders
open scoped NNReal ENNReal
local instance nativeCanonicalGammaEnergy_period : Fact (0<2*Real.pi):=⟨by positivity⟩
local instance nativeCanonicalGammaEnergy_unit : Fact (0<(1:ℝ)):=⟨zero_lt_one⟩
local instance nativeCanonicalGammaEnergy_realSigma : MeasurableSpace RealL2:=borel _
local instance nativeCanonicalGammaEnergy_realBorel : BorelSpace RealL2:=⟨rfl⟩
local instance nativeCanonicalGammaEnergy_nativeSigma : MeasurableSpace CircleL2:=borel _
local instance nativeCanonicalGammaEnergy_nativeBorel : BorelSpace CircleL2:=⟨rfl⟩
local instance nativeCanonicalGammaEnergy_unitSigma : MeasurableSpace CircleHeat.CircleL2:=borel _
local instance nativeCanonicalGammaEnergy_unitBorel : BorelSpace CircleHeat.CircleL2:=⟨rfl⟩
local instance nativeCanonicalGammaEnergy_second : SecondCountableTopology CircleHeat.CircleL2:=
  (_root_.fourierBasis (T:=(1:ℝ))).repr.toHomeomorph.secondCountableTopology
local instance nativeCanonicalGammaEnergy_realSecond : SecondCountableTopology RealL2:=
  FiniteHaar.realCircleIdentification.toHomeomorph.secondCountableTopology
variable {Ω : Type*} [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ]
variable (H v b : ℝ≥0) (hbH : b≤H) (hb1 : (b:ℝ)≤1)
variable (U V : ℝ≥0×Ω→RealL2) (hU : StronglyMeasurable[𝓕.predictable] U) (hV : StronglyMeasurable[𝓕.predictable] V)
variable (P : CanonicalCovariance.ProfileParameters) (Λ κ : ℝ) (hκ : 0<κ) (hκP : κ<P.lower)
variable (I0 I1 : StandardTerminalIto (C:=RealHaarIntegrand.Columns) (E:=RealL2) 𝓕 μ H)

variable (hb0 : 0<b) (hnull : NullCompleteFiltration.ContainsNullSets 𝓕 μ)
variable (B0 B1 : ℝ≥0) (hBDG0 : StandardTerminalBDG16 I0 B0) (hBDG1 : StandardTerminalBDG16 I1 B1)
variable {a : ℝ→ℝ} (ha : BoundedSmooth a) {A β : ℝ} (hA : 0≤A) (hβ : 0≤β) (hβ1 : β≤1)
variable (hh : ∀ x y,|a x-a y|≤A*|x-y|^β) (j : ℕ)
variable {L ρ m W : ℝ} (hL : 1≤L) (hρ : 0<ρ) (hρhalf : ρ<1/2) (hm : 0<m)
variable (hmP : m≤P.lower-κ) (hWP : P.upper-κ≤W)
variable (c0 c1 : ℝ≥0×Ω→FiniteHaar.EllipticField m W)
variable (hc0 : Measurable[𝓕.predictable] c0) (hc1 : Measurable[𝓕.predictable] c1)

def widen (f : FiniteHaar.EllipticField (P.lower-κ) (P.upper-κ)) : FiniteHaar.EllipticField m W:=
  ⟨f.1,f.2.1,f.2.2.mono (fun _ h=>⟨hmP.trans h.1,h.2.trans hWP⟩)⟩
theorem widen_measurable : Measurable (widen P κ hmP hWP):=
  measurable_subtype_coe.subtype_mk

local notation "OldU"=>NativeCanonicalGammaFields.oldU (v:=v) (U:=U)
local notation "OldD"=>NativeCanonicalGammaFields.oldD (v:=v) (U:=U) (V:=V)
local notation "OldUM"=>NativeCanonicalGammaFields.oldU_measurable (𝓕:=𝓕) (v:=v) (U:=U) (hU:=hU)
local notation "OldDM"=>NativeCanonicalGammaFields.oldD_measurable (𝓕:=𝓕) (v:=v) (U:=U) (V:=V) (hU:=hU) (hV:=hV)

def frozen (θ : ℝ) (p : ℝ≥0×Ω) : FiniteHaar.EllipticField m W:=
  widen P κ hmP hWP (FrozenReferenceFields.field P Λ κ θ hκP v (NativeCanonicalReferenceField.data OldU OldD) p)
include hU hV in
theorem frozen_predictable (θ : ℝ) : Measurable[𝓕.predictable]
    (frozen (v:=v) (U:=U) (V:=V) (P:=P) (Λ:=Λ) (κ:=κ) (hκP:=hκP) (hmP:=hmP) (hWP:=hWP) θ):=
  (widen_measurable P κ hmP hWP).comp
    (FrozenReferenceFields.field_predictable 𝓕 P Λ κ θ hκP v _
      (NativeCanonicalReferenceField.data_measurable 𝓕 v OldU OldD OldUM OldDM)).measurable

local notation "G"=>NativeCanonicalGammaFields.fields (𝓕:=𝓕) (μ:=μ) (H:=H) (v:=v) (b:=b) (hbH:=hbH) (hb1:=hb1)
  (U:=U) (V:=V) (hU:=hU) (hV:=hV) (P:=P) (Λ:=Λ) (κ:=κ) (hκ:=hκ) (hκP:=hκP) (I0:=I0) (I1:=I1) a j
local notation "GM"=>NativeCanonicalGammaFields.fields_predictable (𝓕:=𝓕) (μ:=μ) (H:=H) (v:=v) (b:=b) (hbH:=hbH) (hb1:=hb1)
  (U:=U) (V:=V) (hU:=hU) (hV:=hV) (P:=P) (Λ:=Λ) (κ:=κ) (hκ:=hκ) (hκP:=hκP) (I0:=I0) (I1:=I1)
  hb0 hnull B0 B1 hBDG0 hBDG1 a ha j
local notation "GB"=>NativeCanonicalGammaFields.fields_bound (𝓕:=𝓕) (μ:=μ) (H:=H) (v:=v) (b:=b) (hbH:=hbH) (hb1:=hb1)
  (U:=U) (V:=V) (hU:=hU) (hV:=hV) (P:=P) (Λ:=Λ) (κ:=κ) (hκ:=hκ) (hκP:=hκP) (I0:=I0) (I1:=I1)
  ha hA hβ hβ1 hh j
local notation "Cap"=>ScalarHeatSingleMultiplier.cap A β j
local notation "R0"=>frozen (v:=v) (U:=U) (V:=V) (P:=P) (Λ:=Λ) (κ:=κ) (hκP:=hκP) (hmP:=hmP) (hWP:=hWP) 0
local notation "R1"=>frozen (v:=v) (U:=U) (V:=V) (P:=P) (Λ:=Λ) (κ:=κ) (hκP:=hκP) (hmP:=hmP) (hWP:=hWP) 1
local notation "R0M"=>frozen_predictable (𝓕:=𝓕) (hU:=hU) (hV:=hV) (v:=v) (U:=U) (V:=V) (P:=P) (Λ:=Λ) (κ:=κ) (hκP:=hκP) (hmP:=hmP) (hWP:=hWP) 0
local notation "R1M"=>frozen_predictable (𝓕:=𝓕) (hU:=hU) (hV:=hV) (v:=v) (U:=U) (V:=V) (P:=P) (Λ:=Λ) (κ:=κ) (hκP:=hκP) (hmP:=hmP) (hWP:=hWP) 1
local notation "P0"=>NativePairedGammaEnergy.additive 𝓕 μ H v b hbH hb1 hL hρ hρhalf Cap G GM GB κ hκ
local notation "P1"=>NativePairedGammaEnergy.residual 𝓕 μ H v b hbH hb1 hL hρ hρhalf hm Cap G GM GB c0 c1 R0 R1 hc0 hc1 R0M R1M
local notation "Sharp"=>NativeCanonicalGammaSharp.sharp (v:=v) (b:=b) (P:=P) A β j

open NativeFourierIto NativeFourierNoiseRows OrthogonalItoChannels

/-- Complete original-J stochastic paired Gamma with the ACTUAL
corrected current, ACTUAL own-profile references and ACTUAL canonical
remaining variances. Every scalar-field, predictability, ellipticity,
Hilbert-column and stochastic-energy applicability condition is proved.
The two current coefficients remain the true supplied physical fields. -/
theorem complete_energy (J : StandardTerminalIto (C:=Both Row) (E:=ℝ) 𝓕 μ H) :
    ∃ C : ℝ,0<C ∧
    (∫⁻ ω,(∑' l : ℤ,ENNReal.ofReal (‖J.integral (realInput 𝓕 μ H l P0 P1) ω‖^2))+
      (∑' l : ℤ,ENNReal.ofReal (‖J.integral (imagInput 𝓕 μ H l P0 P1) ω‖^2)) ∂μ)≤
      ∫⁻ p,ENNReal.ofReal ((NativeGammaClock.window v b).indicator (fun p=>6*(
        C*(Sharp p)^2*(NativeHeatSpan.clock (NativeGammaClock.age v b p))^(-(1/2:ℝ))*
          NativeSignedHaarProcess.inputEnergy hL hρ.le (c1 p) (c0 p)+
        HaarWeightedHeat.higherConstant m W hm 0 ρ*(Sharp p)^2*
          (NativeHeatSpan.clock (NativeGammaClock.age v b p))^(ρ-1/2)*‖(R0 p).1-(R1 p).1‖^2+
        (κ+W)*((1+2*HeatTrace.fractionalGaussianIntegral ρ)*(NativeGammaClock.age v b p)^(ρ-1/2))*
          (‖NativeRandomRows.nativeRow (G 0) p-NativeRandomRows.nativeRow (G 1) p‖^2+
           ‖NativeRandomRows.nativeRow (G 1) p-NativeRandomRows.nativeRow (G 2) p‖^2+
           ‖NativeRandomRows.nativeRow (G 3) p-NativeRandomRows.nativeRow (G 4) p‖^2+
           ‖NativeRandomRows.nativeRow (G 4) p-NativeRandomRows.nativeRow (G 5) p‖^2))) p) ∂energyMeasure μ H := by
  obtain ⟨C,hC,hE⟩:=NativePairedGammaEnergy.exists_complete_energy_bound 𝓕 μ H v b hbH hb1 hL hρ hρhalf hm
    Cap G GM GB κ hκ c0 c1 R0 R1 hc0 hc1 R0M R1M
  refine ⟨C,hC,hE J Sharp (fun p _=>NativeCanonicalGammaSharp.sharp_nonneg (v:=v) (b:=b) (P:=P) hA β j p) ?_⟩
  exact NativeCanonicalGammaSharp.rows_bound (𝓕:=𝓕) (μ:=μ) (H:=H) (v:=v) (b:=b) (hbH:=hbH) (hb1:=hb1)
    (U:=U) (V:=V) (hU:=hU) (hV:=hV) (P:=P) (Λ:=Λ) (κ:=κ) (hκ:=hκ) (hκP:=hκP) (I0:=I0) (I1:=I1)
    hb0 hnull B0 B1 hBDG0 hBDG1 ha hA hβ hβ1 hh j

end SHE.NativeCanonicalGammaEnergy

