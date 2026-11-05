module

public import SHE.NativeCanonicalVarianceField
public import SHE.NativeCorrectedCurrentFields
public import SHE.NativePairedGammaEnergy

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2500000
namespace SHE.NativeCanonicalGammaFields
open Set MeasureTheory PredictableL2 NativeHeatObservation DyadicApproximation StoppedFourier SmoothCylinders
open scoped NNReal ENNReal
local instance nativeCanonicalGammaFields_period : Fact (0<2*Real.pi):=⟨by positivity⟩
local instance nativeCanonicalGammaFields_unit : Fact (0<(1:ℝ)):=⟨zero_lt_one⟩
local instance nativeCanonicalGammaFields_realSigma : MeasurableSpace RealL2:=borel _
local instance nativeCanonicalGammaFields_realBorel : BorelSpace RealL2:=⟨rfl⟩
local instance nativeCanonicalGammaFields_nativeSigma : MeasurableSpace CircleL2:=borel _
local instance nativeCanonicalGammaFields_nativeBorel : BorelSpace CircleL2:=⟨rfl⟩
local instance nativeCanonicalGammaFields_unitSigma : MeasurableSpace CircleHeat.CircleL2:=borel _
local instance nativeCanonicalGammaFields_unitBorel : BorelSpace CircleHeat.CircleL2:=⟨rfl⟩
local instance nativeCanonicalGammaFields_second : SecondCountableTopology CircleHeat.CircleL2:=
  (_root_.fourierBasis (T:=(1:ℝ))).repr.toHomeomorph.secondCountableTopology
local instance nativeCanonicalGammaFields_realSecond : SecondCountableTopology RealL2:=
  FiniteHaar.realCircleIdentification.toHomeomorph.secondCountableTopology
variable {Ω : Type*} [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ]
variable (H v b : ℝ≥0) (hbH : b≤H) (hb1 : (b:ℝ)≤1)
variable (U V : ℝ≥0×Ω→RealL2) (hU : StronglyMeasurable[𝓕.predictable] U) (hV : StronglyMeasurable[𝓕.predictable] V)
variable (P : CanonicalCovariance.ProfileParameters) (Λ κ : ℝ) (hκ : 0<κ) (hκP : κ<P.lower)
variable (I0 I1 : StandardTerminalIto (C:=RealHaarIntegrand.Columns) (E:=RealL2) 𝓕 μ H)

def oldU (ω : Ω) : RealL2:=U (v,ω)
def oldD (ω : Ω) : RealL2:=V (v,ω)-U (v,ω)

include hU in
theorem oldU_measurable : Measurable[𝓕 v] (oldU (v:=v) (U:=U)):=
  ((show IsStronglyPredictable 𝓕 (Function.curry U) from hU).stronglyAdapted v).measurable
include hU hV in
theorem oldD_measurable : Measurable[𝓕 v] (oldD (v:=v) (U:=U) (V:=V)):=
  NativeCorrectedCurrentFields.pastD_measurable 𝓕 U V hU hV v

local notation "u"=>oldU (v:=v) (U:=U)
local notation "d"=>oldD (v:=v) (U:=U) (V:=V)
local notation "hu"=>oldU_measurable (𝓕:=𝓕) (v:=v) (U:=U) (hU:=hU)
local notation "hd"=>oldD_measurable (𝓕:=𝓕) (v:=v) (U:=U) (V:=V) (hU:=hU) (hV:=hV)

def variance (θ : ℝ) : (ℝ≥0×Ω)×HeatCircle→ℝ:=NativeCanonicalVarianceField.field P Λ θ v b u d
def current (θ : ℝ) : (ℝ≥0×Ω)×HeatCircle→ℝ:=
  PredictableScalarField.nativeField (NativeCorrectedCurrentFields.state U V Λ θ v b)
def reference (θ : ℝ) : (ℝ≥0×Ω)×HeatCircle→ℝ:=
  PredictableScalarField.nativeField
    (NativeCanonicalReferenceField.state 𝓕 μ H b v P Λ κ hκ hκP u d hu hd hbH hb1 I0 I1 θ)

include hU hV in
theorem variance_predictable (θ : ℝ) :
    @Measurable _ ℝ (𝓕.predictable.prod inferInstance) _ (variance (v:=v) (b:=b) (U:=U) (V:=V) (P:=P) (Λ:=Λ) θ):=
  NativeCanonicalVarianceField.field_predictable 𝓕 P Λ θ v b u d hu hd
include hU hV in
theorem current_predictable (θ : ℝ) :
    @Measurable _ ℝ (𝓕.predictable.prod inferInstance) _ (current (v:=v) (b:=b) (U:=U) (V:=V) (Λ:=Λ) θ):=
  NativeCorrectedCurrentFields.scalar_predictable 𝓕 U V hU hV Λ θ v b
theorem reference_predictable (hb0 : 0<b) (hnull : NullCompleteFiltration.ContainsNullSets 𝓕 μ)
    (B0 B1 : ℝ≥0) (hBDG0 : StandardTerminalBDG16 I0 B0) (hBDG1 : StandardTerminalBDG16 I1 B1) (θ : ℝ) :
    @Measurable _ ℝ (𝓕.predictable.prod inferInstance) _
      (reference (𝓕:=𝓕) (μ:=μ) (H:=H) (v:=v) (b:=b) (hbH:=hbH) (hb1:=hb1) (U:=U) (V:=V) (hU:=hU) (hV:=hV) (P:=P) (Λ:=Λ) (κ:=κ) (hκ:=hκ) (hκP:=hκP) (I0:=I0) (I1:=I1) θ):=
  NativeCanonicalReferenceField.scalar_predictable 𝓕 μ H b v P Λ κ hκ hκP u d hu hd hbH hb1 I0 I1
    hb0 hnull B0 B1 hBDG0 hBDG1 θ

def fields (a : ℝ→ℝ) (j : ℕ) : Fin 6→(ℝ≥0×Ω)×HeatCircle→ℂ:=
  ScalarHeatSixFields.fields a j (variance (v:=v) (b:=b) (U:=U) (V:=V) (P:=P) (Λ:=Λ) 0) (variance (v:=v) (b:=b) (U:=U) (V:=V) (P:=P) (Λ:=Λ) 1)
    (current (v:=v) (b:=b) (U:=U) (V:=V) (Λ:=Λ) 0) (current (v:=v) (b:=b) (U:=U) (V:=V) (Λ:=Λ) 1)
    (reference (𝓕:=𝓕) (μ:=μ) (H:=H) (v:=v) (b:=b) (hbH:=hbH) (hb1:=hb1) (U:=U) (V:=V) (hU:=hU) (hV:=hV) (P:=P) (Λ:=Λ) (κ:=κ) (hκ:=hκ) (hκP:=hκP) (I0:=I0) (I1:=I1) 0)
    (reference (𝓕:=𝓕) (μ:=μ) (H:=H) (v:=v) (b:=b) (hbH:=hbH) (hb1:=hb1) (U:=U) (V:=V) (hU:=hU) (hV:=hV) (P:=P) (Λ:=Λ) (κ:=κ) (hκ:=hκ) (hκP:=hκP) (I0:=I0) (I1:=I1) 1)

theorem fields_predictable (hb0 : 0<b) (hnull : NullCompleteFiltration.ContainsNullSets 𝓕 μ)
    (B0 B1 : ℝ≥0) (hBDG0 : StandardTerminalBDG16 I0 B0) (hBDG1 : StandardTerminalBDG16 I1 B1)
    (a : ℝ→ℝ) (ha : BoundedSmooth a) (j : ℕ) (i : Fin 6) :
    @Measurable _ ℂ (𝓕.predictable.prod inferInstance) _
      (fields (𝓕:=𝓕) (μ:=μ) (H:=H) (v:=v) (b:=b) (hbH:=hbH) (hb1:=hb1) (U:=U) (V:=V) (hU:=hU) (hV:=hV) (P:=P) (Λ:=Λ) (κ:=κ) (hκ:=hκ) (hκP:=hκP) (I0:=I0) (I1:=I1) a j i) := by
  letI : MeasurableSpace (ℝ≥0×Ω):=𝓕.predictable
  exact ScalarHeatSixFields.measurable ha j (variance_predictable (𝓕:=𝓕) (v:=v) (b:=b) (U:=U) (V:=V) (hU:=hU) (hV:=hV) (P:=P) (Λ:=Λ) 0)
    (variance_predictable (𝓕:=𝓕) (v:=v) (b:=b) (U:=U) (V:=V) (hU:=hU) (hV:=hV) (P:=P) (Λ:=Λ) 1) (current_predictable (𝓕:=𝓕) (v:=v) (b:=b) (U:=U) (V:=V) (hU:=hU) (hV:=hV) (Λ:=Λ) 0)
    (current_predictable (𝓕:=𝓕) (v:=v) (b:=b) (U:=U) (V:=V) (hU:=hU) (hV:=hV) (Λ:=Λ) 1)
    (reference_predictable (𝓕:=𝓕) (μ:=μ) (H:=H) (v:=v) (b:=b) (hbH:=hbH) (hb1:=hb1) (U:=U) (V:=V) (hU:=hU) (hV:=hV) (P:=P) (Λ:=Λ) (κ:=κ) (hκ:=hκ) (hκP:=hκP) (I0:=I0) (I1:=I1) hb0 hnull B0 B1 hBDG0 hBDG1 0)
    (reference_predictable (𝓕:=𝓕) (μ:=μ) (H:=H) (v:=v) (b:=b) (hbH:=hbH) (hb1:=hb1) (U:=U) (V:=V) (hU:=hU) (hV:=hV) (P:=P) (Λ:=Λ) (κ:=κ) (hκ:=hκ) (hκP:=hκP) (I0:=I0) (I1:=I1) hb0 hnull B0 B1 hBDG0 hBDG1 1) i

theorem fields_bound {a : ℝ→ℝ} (ha : BoundedSmooth a) {A β : ℝ}
    (hA : 0≤A) (hβ : 0≤β) (hβ1 : β≤1) (hh : ∀ x y,|a x-a y|≤A*|x-y|^β)
    (j : ℕ) (i : Fin 6) (p : ℝ≥0×Ω) (x : HeatCircle) :
    ‖fields (𝓕:=𝓕) (μ:=μ) (H:=H) (v:=v) (b:=b) (hbH:=hbH) (hb1:=hb1) (U:=U) (V:=V) (hU:=hU) (hV:=hV) (P:=P) (Λ:=Λ) (κ:=κ) (hκ:=hκ) (hκP:=hκP) (I0:=I0) (I1:=I1) a j i (p,x)‖≤
      ScalarHeatSingleMultiplier.cap A β j:=ScalarHeatSixFields.bound ha hA hβ hβ1 hh j _ _ _ _ _ _ i p x

end SHE.NativeCanonicalGammaFields
