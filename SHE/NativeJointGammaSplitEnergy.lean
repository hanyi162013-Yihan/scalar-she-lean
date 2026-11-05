module

public import SHE.NativeCanonicalGammaEnergy
public import SHE.NativeConvexGammaUniform
public import SHE.NativeJointGammaSharp
public import SHE.NativeGammaDamping
public import SHE.NativeJointGammaAgeSplit
public import SHE.NativeJointGammaEnergy

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2500000
namespace SHE.NativeJointGammaSplitEnergy
open Set MeasureTheory PredictableL2 NativeHeatObservation DyadicApproximation StoppedFourier SmoothCylinders
open scoped NNReal ENNReal
local instance nativeCanonicalGammaUniform_period : Fact (0<2*Real.pi):=⟨by positivity⟩
local instance nativeCanonicalGammaUniform_unit : Fact (0<(1:ℝ)):=⟨zero_lt_one⟩
local instance nativeCanonicalGammaUniform_realSigma : MeasurableSpace RealL2:=borel _
local instance nativeCanonicalGammaUniform_realBorel : BorelSpace RealL2:=⟨rfl⟩
local instance nativeCanonicalGammaUniform_nativeSigma : MeasurableSpace CircleL2:=borel _
local instance nativeCanonicalGammaUniform_nativeBorel : BorelSpace CircleL2:=⟨rfl⟩
local instance nativeCanonicalGammaUniform_unitSigma : MeasurableSpace CircleHeat.CircleL2:=borel _
local instance nativeCanonicalGammaUniform_unitBorel : BorelSpace CircleHeat.CircleL2:=⟨rfl⟩
local instance nativeCanonicalGammaUniform_second : SecondCountableTopology CircleHeat.CircleL2:=
  (_root_.fourierBasis (T:=(1:ℝ))).repr.toHomeomorph.secondCountableTopology
local instance nativeCanonicalGammaUniform_realSecond : SecondCountableTopology RealL2:=
  FiniteHaar.realCircleIdentification.toHomeomorph.secondCountableTopology
variable {Ω : Type*} [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ]
variable (H v b : ℝ≥0) (hbH : b≤H) (hb1 : (b:ℝ)≤1)
variable (U V : ℝ≥0×Ω→RealL2) (hU : StronglyMeasurable[𝓕.predictable] U) (hV : StronglyMeasurable[𝓕.predictable] V)
variable (P : CanonicalCovariance.ProfileParameters) (Λ κ : ℝ) (hκ : 0<κ) (hκP : κ<P.lower)
variable (hΛdamp:0≤Λ)
variable (I0 I1 : StandardTerminalIto (C:=RealHaarIntegrand.Columns) (E:=RealL2) 𝓕 μ H)

variable (hb0 : 0<b) (hnull : NullCompleteFiltration.ContainsNullSets 𝓕 μ)
variable (B0 B1 : ℝ≥0) (hBDG0 : StandardTerminalBDG16 I0 B0) (hBDG1 : StandardTerminalBDG16 I1 B1)
variable {a : ℝ→ℝ} (ha : BoundedSmooth a) {A β : ℝ} (hA : 0≤A) (hβ : 0≤β) (hβ1 : β≤1)
variable (hh : ∀ x y,|a x-a y|≤A*|x-y|^β) (j : ℕ)
variable {L ρ m W : ℝ} (hL : 1≤L) (hρ : 0<ρ) (hρhalf : ρ<1/2) (hm : 0<m)
variable (hmP : m≤P.lower-κ) (hWP : P.upper-κ≤W)
variable (c0 c1 : ℝ≥0×Ω→FiniteHaar.EllipticField m W)
variable (hc0 : Measurable[𝓕.predictable] c0) (hc1 : Measurable[𝓕.predictable] c1)

open NativeCanonicalGammaEnergy
local notation "G"=>NativeJointGammaFields.fields (𝓕:=𝓕) (μ:=μ) (H:=H) (v:=v) (b:=b) (hbH:=hbH) (hb1:=hb1)
  (U:=U) (V:=V) (hU:=hU) (hV:=hV) (P:=P) (Λ:=Λ) (κ:=κ) (hκ:=hκ) (hκP:=hκP) (I0:=I0) (I1:=I1) a j
local notation "GM"=>NativeJointGammaFields.fields_predictable (𝓕:=𝓕) (μ:=μ) (H:=H) (v:=v) (b:=b) (hbH:=hbH) (hb1:=hb1)
  (U:=U) (V:=V) (hU:=hU) (hV:=hV) (P:=P) (Λ:=Λ) (κ:=κ) (hκ:=hκ) (hκP:=hκP) (I0:=I0) (I1:=I1)
  hb0 hnull B0 B1 hBDG0 hBDG1 a ha j
local notation "GB"=>NativeJointGammaFields.fields_bound (𝓕:=𝓕) (μ:=μ) (H:=H) (v:=v) (b:=b) (hbH:=hbH) (hb1:=hb1)
  (U:=U) (V:=V) (hU:=hU) (hV:=hV) (P:=P) (Λ:=Λ) (κ:=κ) (hκ:=hκ) (hκP:=hκP) (I0:=I0) (I1:=I1)
  ha hA hβ hβ1 hh j
local notation "Cap"=>ScalarHeatSingleMultiplier.cap A β j
local notation "R0"=>frozen (v:=v) (U:=U) (V:=V) (P:=P) (Λ:=Λ) (κ:=κ) (hκP:=hκP) (hmP:=hmP) (hWP:=hWP) 0
local notation "R1"=>frozen (v:=v) (U:=U) (V:=V) (P:=P) (Λ:=Λ) (κ:=κ) (hκP:=hκP) (hmP:=hmP) (hWP:=hWP) 1
local notation "R0M"=>frozen_predictable (𝓕:=𝓕) (hU:=hU) (hV:=hV) (v:=v) (U:=U) (V:=V) (P:=P) (Λ:=Λ) (κ:=κ) (hκP:=hκP) (hmP:=hmP) (hWP:=hWP) 0
local notation "R1M"=>frozen_predictable (𝓕:=𝓕) (hU:=hU) (hV:=hV) (v:=v) (U:=U) (V:=V) (P:=P) (Λ:=Λ) (κ:=κ) (hκP:=hκP) (hmP:=hmP) (hWP:=hWP) 1
local notation "Damping"=>NativeGammaDamping.value (Ω:=Ω) Λ v b
local notation "DampingM"=>NativeGammaDamping.measurable 𝓕 Λ v b
local notation "Damping0"=>NativeGammaDamping.nonneg (Ω:=Ω) Λ v b
local notation "Damping1"=>NativeGammaDamping.le_one (Ω:=Ω) Λ v b hΛdamp
local notation "P0"=>NativePairedGammaEnergy.additive 𝓕 μ H v b hbH hb1 hL hρ hρhalf Cap G GM GB κ hκ
local notation "P1"=>NativeConvexGammaEnergy.residual 𝓕 μ H v b hbH hb1 hL hρ hρhalf hm Cap G GM GB Damping DampingM Damping0 Damping1 c0 c1 R0 R1 hc0 hc1 R0M R1M
local notation "Sharp"=>NativeJointGammaSharp.sharp (v:=v) (b:=b) (P:=P) A β j

open NativeFourierIto NativeFourierNoiseRows OrthogonalItoChannels

local notation "Signed"=>NativeJointGammaAgeSplit.signed (v:=v) (b:=b) (P:=P) (A:=A) (β:=β) (j:=j) hL hρ hρhalf hm c0 c1
local notation "Frozen"=>NativeJointGammaAgeSplit.frozen (v:=v) (b:=b) (U:=U) (V:=V) (P:=P) (Λ:=Λ) (κ:=κ) (hκP:=hκP)
  (hmP:=hmP) (hWP:=hWP) (A:=A) (β:=β) (j:=j) (ρ:=ρ) hm
local notation "Row"=>NativeJointGammaAgeSplit.row (𝓕:=𝓕) (μ:=μ) (H:=H) (v:=v) (b:=b) (hbH:=hbH) (hb1:=hb1)
  (U:=U) (V:=V) (hU:=hU) (hV:=hV) (P:=P) (Λ:=Λ) (κ:=κ) (hκ:=hκ) (hκP:=hκP) (I0:=I0) (I1:=I1) (a:=a) (ρ:=ρ) j
local notation "Ksum"=>(κ+W)*(1+2*HeatTrace.fractionalGaussianIntegral ρ)


include hb0 hnull B0 B1 hBDG0 hBDG1 ha hA hβ hβ1 hh hc0 hc1 hΛdamp in
/-- The COMPLETE original-J literal joint Gamma energy split into its
actual signed-factor, frozen-factor and four native row positive
budgets. Every field/measurability/isometry condition is derived; no
analytical Gamma bound is inserted as an assumption. -/
def complete_energy (J:StandardTerminalIto (C:=Both NativeFourierNoiseRows.Row) (E:=ℝ) 𝓕 μ H) :=
  let Cbudget:ℝ≥0∞:=6*((∫⁻τ in Ioc (0:ℝ) ((b:ℝ)-(v:ℝ)),∫⁻ω,ENNReal.ofReal (Signed (τ,ω)) ∂μ)+
      (∫⁻τ in Ioc (0:ℝ) ((b:ℝ)-(v:ℝ)),∫⁻ω,ENNReal.ofReal (Frozen (τ,ω)) ∂μ)+
      ENNReal.ofReal Ksum*((∫⁻τ in Ioc (0:ℝ) ((b:ℝ)-(v:ℝ)),∫⁻ω,ENNReal.ofReal (Row 0 1 (τ,ω)) ∂μ)+
        (∫⁻τ in Ioc (0:ℝ) ((b:ℝ)-(v:ℝ)),∫⁻ω,ENNReal.ofReal (Row 1 2 (τ,ω)) ∂μ)+
        (∫⁻τ in Ioc (0:ℝ) ((b:ℝ)-(v:ℝ)),∫⁻ω,ENNReal.ofReal (Row 3 4 (τ,ω)) ∂μ)+
        (∫⁻τ in Ioc (0:ℝ) ((b:ℝ)-(v:ℝ)),∫⁻ω,ENNReal.ofReal (Row 4 5 (τ,ω)) ∂μ)))
  (NativeGammaAgeBound.bound μ H v b hbH
    (NativeJointGammaEnergy.complete_energy
    (𝓕:=𝓕) (μ:=μ) (H:=H) (v:=v) (b:=b) (hbH:=hbH) (hb1:=hb1) (U:=U)
    (V:=V) (hU:=hU) (hV:=hV) (P:=P) (Λ:=Λ) (κ:=κ) (hκ:=hκ) (hκP:=hκP)
    (I0:=I0) (I1:=I1) (hb0:=hb0) (hnull:=hnull) (B0:=B0) (B1:=B1) (hBDG0:=hBDG0) (hBDG1:=hBDG1)
    (ha:=ha) (hA:=hA) (hβ:=hβ) (hβ1:=hβ1) (hh:=hh) (j:=j) (L:=L) (ρ:=ρ)
    (m:=m) (W:=W) (hL:=hL) (hρ:=hρ) (hρhalf:=hρhalf) (hm:=hm) (hmP:=hmP) (hWP:=hWP)
    (c0:=c0) (c1:=c1) (hc0:=hc0) (hc1:=hc1) (hΛdamp:=hΛdamp) J)).trans (c:=Cbudget) (by
      have hS:=NativeJointGammaAgeSplit.split
          (𝓕:=𝓕) (μ:=μ) (H:=H) (v:=v) (b:=b) (hbH:=hbH) (hb1:=hb1) (U:=U)
          (V:=V) (hU:=hU) (hV:=hV) (P:=P) (Λ:=Λ) (κ:=κ) (hκ:=hκ) (hκP:=hκP)
          (I0:=I0) (I1:=I1) (hb0:=hb0) (hnull:=hnull) (B0:=B0) (B1:=B1) (hBDG0:=hBDG0) (hBDG1:=hBDG1)
          (ha:=ha) (hA:=hA) (hβ:=hβ) (hβ1:=hβ1) (hh:=hh) (j:=j) (L:=L) (ρ:=ρ)
          (m:=m) (W:=W) (hL:=hL) (hρ:=hρ) (hρhalf:=hρhalf) (hm:=hm) (hmP:=hmP) (hWP:=hWP)
          (c0:=c0) (c1:=c1) (hc0:=hc0) (hc1:=hc1)
      convert hS using 1
      apply lintegral_congr
      intro τ
      apply lintegral_congr
      intro ω
      congr 1
      dsimp only [NativeJointGammaAgeSplit.signed,NativeJointGammaAgeSplit.frozen,
        NativeJointGammaAgeSplit.row,NativeJointGammaAgeSplit.reflected]
      ring)
end SHE.NativeJointGammaSplitEnergy
