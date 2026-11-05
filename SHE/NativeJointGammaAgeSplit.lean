module

public import SHE.NativeCanonicalGammaEnergy
public import SHE.NativeConvexGammaUniform
public import SHE.NativeJointGammaSharp
public import SHE.NativeGammaDamping
public import SHE.NativeGammaAgeBound
public import SHE.GammaPositiveIteratedSplit

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2500000
namespace SHE.NativeJointGammaAgeSplit
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
local instance nativeGammaAgeSplit_nativeSecond : SecondCountableTopology CircleL2:=
  (_root_.fourierBasis (T:=2*Real.pi)).repr.toHomeomorph.secondCountableTopology
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
local notation "R0"=>NativeCanonicalGammaEnergy.frozen (v:=v) (U:=U) (V:=V) (P:=P) (Λ:=Λ) (κ:=κ) (hκP:=hκP) (hmP:=hmP) (hWP:=hWP) 0
local notation "R1"=>NativeCanonicalGammaEnergy.frozen (v:=v) (U:=U) (V:=V) (P:=P) (Λ:=Λ) (κ:=κ) (hκP:=hκP) (hmP:=hmP) (hWP:=hWP) 1
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

def reflected (p:ℝ×Ω):ℝ≥0×Ω:=(((b:ℝ)-p.1).toNNReal,p.2)
local notation "Q"=>reflected (Ω:=Ω) b
local notation "Ctrace"=>NativeConvexGammaUniform.constant m W hm hρ hρhalf

def signed (p:ℝ×Ω):ℝ:=Ctrace*(Sharp (Q p))^2*(NativeHeatSpan.clock (NativeGammaClock.age v b (Q p)))^(-(1/2:ℝ))*
  NativeSignedHaarProcess.inputEnergy hL hρ.le (c1 (Q p)) (c0 (Q p))
def frozen (p:ℝ×Ω):ℝ:=HaarWeightedHeat.higherConstant m W hm 0 ρ*(Sharp (Q p))^2*
  (NativeHeatSpan.clock (NativeGammaClock.age v b (Q p)))^(ρ-1/2)*‖(R0 (Q p)).1-(R1 (Q p)).1‖^2
def row (i l:Fin 6) (p:ℝ×Ω):ℝ:=(NativeGammaClock.age v b (Q p))^(ρ-1/2)*
  ‖NativeRandomRows.nativeRow (G i) (Q p)-NativeRandomRows.nativeRow (G l) (Q p)‖^2

theorem reflected_measurable:Measurable (Q):=
  (measurable_real_toNNReal.comp (measurable_const.sub measurable_fst)).prodMk measurable_snd

include hc0 hc1 in
theorem signed_measurable:Measurable (signed (v:=v) (b:=b) (P:=P) (A:=A) (β:=β) (j:=j) hL hρ hρhalf hm c0 c1):=by
  have ha:Measurable (fun p:ℝ×Ω=>NativeGammaClock.age v b (Q p)):=
    ((NativeGammaClock.age_measurable 𝓕 v b).mono (predictable_le_product 𝓕) le_rfl).comp (reflected_measurable b)
  have hs:Measurable (fun p:ℝ×Ω=>Sharp (Q p)):=by
    unfold NativeJointGammaSharp.sharp NativeJointGammaSharp.lower ScalarHeatBandEnvelope.decay
    fun_prop
  have he:Measurable (fun p:ℝ×Ω=>NativeSignedHaarProcess.inputEnergy hL hρ.le (c1 (Q p)) (c0 (Q p))):=
    (NativeSignedHaarProcess.inputEnergy_measurable hL hρ.le c1 c0
      (hc1.mono (predictable_le_product 𝓕) le_rfl)
      (hc0.mono (predictable_le_product 𝓕) le_rfl)).comp (reflected_measurable b)
  unfold signed NativeHeatSpan.clock
  fun_prop

include hU hV in
theorem frozen_measurable:Measurable (frozen (v:=v) (b:=b) (U:=U) (V:=V) (P:=P) (Λ:=Λ) (κ:=κ) (hκP:=hκP)
    (hmP:=hmP) (hWP:=hWP) (A:=A) (β:=β) (j:=j) (ρ:=ρ) hm):=by
  have ha:Measurable (fun p:ℝ×Ω=>NativeGammaClock.age v b (Q p)):=
    ((NativeGammaClock.age_measurable 𝓕 v b).mono (predictable_le_product 𝓕) le_rfl).comp (reflected_measurable b)
  have hs:Measurable (fun p:ℝ×Ω=>Sharp (Q p)):=by
    unfold NativeJointGammaSharp.sharp NativeJointGammaSharp.lower ScalarHeatBandEnvelope.decay
    fun_prop
  have h0:Measurable (fun p:ℝ×Ω=>(R0 (Q p)).1):=
    (measurable_subtype_coe.comp ((R0M).mono (predictable_le_product 𝓕) le_rfl)).comp (reflected_measurable b)
  have h1:Measurable (fun p:ℝ×Ω=>(R1 (Q p)).1):=
    (measurable_subtype_coe.comp ((R1M).mono (predictable_le_product 𝓕) le_rfl)).comp (reflected_measurable b)
  unfold frozen NativeHeatSpan.clock
  fun_prop

include hb0 hnull B0 B1 hBDG0 hBDG1 ha hA hβ hβ1 hh in
theorem row_measurable (i l:Fin 6):Measurable (row (𝓕:=𝓕) (μ:=μ) (H:=H) (v:=v) (b:=b) (hbH:=hbH) (hb1:=hb1)
    (U:=U) (V:=V) (hU:=hU) (hV:=hV) (P:=P) (Λ:=Λ) (κ:=κ) (hκ:=hκ) (hκP:=hκP) (I0:=I0) (I1:=I1) (a:=a) (ρ:=ρ) j i l):=by
  have hn(n:Fin 6):Measurable (fun p:ℝ×Ω=>NativeRandomRows.nativeRow (G n) (Q p)):=by
    have hp:@Measurable (ℝ≥0×Ω) CircleL2 𝓕.predictable (borel CircleL2) (NativeRandomRows.nativeRow (G n)):=by
      letI:MeasurableSpace (ℝ≥0×Ω):=𝓕.predictable
      exact NativeRandomRows.nativeRow_measurable (GM n) (GB n)
    exact (hp.mono (predictable_le_product 𝓕) le_rfl).comp (reflected_measurable b)
  have ht:Measurable (fun p:ℝ×Ω=>NativeGammaClock.age v b (Q p)):=
    ((NativeGammaClock.age_measurable 𝓕 v b).mono (predictable_le_product 𝓕) le_rfl).comp (reflected_measurable b)
  exact (ht.pow_const _).mul (((hn i).sub (hn l)).norm.pow_const 2)
local notation "Signed"=>signed (v:=v) (b:=b) (P:=P) (A:=A) (β:=β) (j:=j) hL hρ hρhalf hm c0 c1
local notation "Frozen"=>frozen (v:=v) (b:=b) (U:=U) (V:=V) (P:=P) (Λ:=Λ) (κ:=κ) (hκP:=hκP)
  (hmP:=hmP) (hWP:=hWP) (A:=A) (β:=β) (j:=j) (ρ:=ρ) hm
local notation "Row"=>row (𝓕:=𝓕) (μ:=μ) (H:=H) (v:=v) (b:=b) (hbH:=hbH) (hb1:=hb1)
  (U:=U) (V:=V) (hU:=hU) (hV:=hV) (P:=P) (Λ:=Λ) (κ:=κ) (hκ:=hκ) (hκP:=hκP) (I0:=I0) (I1:=I1) (a:=a) (ρ:=ρ) j
local notation "Ksum"=>(κ+W)*(1+2*HeatTrace.fractionalGaussianIntegral ρ)

include hc0 hc1 hb0 hnull B0 B1 hBDG0 hBDG1 ha hA hβ hβ1 hh in
/-- Exact six-term splitting at a fixed original past. Every joint Borel
condition follows from the actual predictable fields and their proved
bounds. The trace constant is chosen before every field and clock. -/
theorem split:
    (∫⁻τ in Ioc (0:ℝ) ((b:ℝ)-(v:ℝ)),∫⁻ω,ENNReal.ofReal
      (6*(Signed (τ,ω)+Frozen (τ,ω)+Ksum*(Row 0 1 (τ,ω)+Row 1 2 (τ,ω)+Row 3 4 (τ,ω)+Row 4 5 (τ,ω)))) ∂μ)≤
    6*((∫⁻τ in Ioc (0:ℝ) ((b:ℝ)-(v:ℝ)),∫⁻ω,ENNReal.ofReal (Signed (τ,ω)) ∂μ)+
      (∫⁻τ in Ioc (0:ℝ) ((b:ℝ)-(v:ℝ)),∫⁻ω,ENNReal.ofReal (Frozen (τ,ω)) ∂μ)+
      ENNReal.ofReal Ksum*((∫⁻τ in Ioc (0:ℝ) ((b:ℝ)-(v:ℝ)),∫⁻ω,ENNReal.ofReal (Row 0 1 (τ,ω)) ∂μ)+
        (∫⁻τ in Ioc (0:ℝ) ((b:ℝ)-(v:ℝ)),∫⁻ω,ENNReal.ofReal (Row 1 2 (τ,ω)) ∂μ)+
        (∫⁻τ in Ioc (0:ℝ) ((b:ℝ)-(v:ℝ)),∫⁻ω,ENNReal.ofReal (Row 3 4 (τ,ω)) ∂μ)+
        (∫⁻τ in Ioc (0:ℝ) ((b:ℝ)-(v:ℝ)),∫⁻ω,ENNReal.ofReal (Row 4 5 (τ,ω)) ∂μ))):=by
  have hs:Measurable Signed:=signed_measurable (𝓕:=𝓕) (v:=v) (b:=b) (P:=P) (j:=j) hL hρ hρhalf hm c0 c1 hc0 hc1
  have hf:Measurable Frozen:=frozen_measurable (𝓕:=𝓕) (v:=v) (b:=b) (U:=U) (V:=V) (hU:=hU) (hV:=hV)
    (P:=P) (Λ:=Λ) (κ:=κ) (hκP:=hκP) (hmP:=hmP) (hWP:=hWP) (j:=j) (ρ:=ρ) hm
  have hr(i l:Fin 6):Measurable (Row i l):=row_measurable (𝓕:=𝓕) (μ:=μ) (H:=H) (v:=v) (b:=b) (hbH:=hbH) (hb1:=hb1)
    (U:=U) (V:=V) (hU:=hU) (hV:=hV) (P:=P) (Λ:=Λ) (κ:=κ) (hκ:=hκ) (hκP:=hκP) (I0:=I0) (I1:=I1)
    (hb0:=hb0) (hnull:=hnull) (B0:=B0) (B1:=B1) (hBDG0:=hBDG0) (hBDG1:=hBDG1)
    (ha:=ha) (hA:=hA) (hβ:=hβ) (hβ1:=hβ1) (hh:=hh) (j:=j) (ρ:=ρ) i l
  letI:Nonempty Ω:=nonempty_of_isProbabilityMeasure μ
  have hW:0≤W:=FiniteHaar.elliptic_upper_nonneg (c0 (0,Classical.arbitrary Ω)).1 m W hm (c0 (0,Classical.arbitrary Ω)).2.2
  have hK:0≤Ksum:=mul_nonneg (add_nonneg hκ.le hW) (by linarith [HeatTrace.fractionalGaussianIntegral_pos hρhalf])
  exact GammaPositiveIteratedSplit.split (volume.restrict (Ioc (0:ℝ) ((b:ℝ)-(v:ℝ)))) μ
    Signed Frozen (Row 0 1) (Row 1 2) (Row 3 4) (Row 4 5) hs hf (hr 0 1) (hr 1 2) (hr 3 4) (hr 4 5) hK
end SHE.NativeJointGammaAgeSplit
