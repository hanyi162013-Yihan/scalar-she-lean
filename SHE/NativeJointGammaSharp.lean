module

public import SHE.NativeJointGammaFields

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2500000
namespace SHE.NativeJointGammaSharp
open Set MeasureTheory PredictableL2 NativeHeatObservation DyadicApproximation StoppedFourier SmoothCylinders
open scoped NNReal ENNReal
local instance nativeJointGammaSharp_period : Fact (0<2*Real.pi):=⟨by positivity⟩
local instance nativeJointGammaSharp_unit : Fact (0<(1:ℝ)):=⟨zero_lt_one⟩
local instance nativeJointGammaSharp_realSigma : MeasurableSpace RealL2:=borel _
local instance nativeJointGammaSharp_realBorel : BorelSpace RealL2:=⟨rfl⟩
local instance nativeJointGammaSharp_nativeSigma : MeasurableSpace CircleL2:=borel _
local instance nativeJointGammaSharp_nativeBorel : BorelSpace CircleL2:=⟨rfl⟩
local instance nativeJointGammaSharp_unitSigma : MeasurableSpace CircleHeat.CircleL2:=borel _
local instance nativeJointGammaSharp_unitBorel : BorelSpace CircleHeat.CircleL2:=⟨rfl⟩
local instance nativeJointGammaSharp_second : SecondCountableTopology CircleHeat.CircleL2:=
  (_root_.fourierBasis (T:=(1:ℝ))).repr.toHomeomorph.secondCountableTopology
local instance nativeJointGammaSharp_realSecond : SecondCountableTopology RealL2:=
  FiniteHaar.realCircleIdentification.toHomeomorph.secondCountableTopology
variable {Ω : Type*} [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ]
variable (H v b : ℝ≥0) (hbH : b≤H) (hb1 : (b:ℝ)≤1)
variable (U V : ℝ≥0×Ω→RealL2) (hU : StronglyMeasurable[𝓕.predictable] U) (hV : StronglyMeasurable[𝓕.predictable] V)
variable (P : CanonicalCovariance.ProfileParameters) (Λ κ : ℝ) (hκ : 0<κ) (hκP : κ<P.lower)
variable (I0 I1 : StandardTerminalIto (C:=RealHaarIntegrand.Columns) (E:=RealL2) 𝓕 μ H)

local notation "u"=>NativeJointGammaFields.oldU (v:=v) (U:=U)
local notation "d"=>NativeJointGammaFields.oldD (v:=v) (U:=U) (V:=V)
local notation "Variance" θ=>NativeJointGammaFields.variance (v:=v) (b:=b) (U:=U) (V:=V) (P:=P) (Λ:=Λ) θ
local notation "Current" θ=>NativeJointGammaFields.current (v:=v) (b:=b) (U:=U) (V:=V) (Λ:=Λ) θ
local notation "Reference" θ=>NativeJointGammaFields.reference
  (𝓕:=𝓕) (μ:=μ) (H:=H) (v:=v) (b:=b) (hbH:=hbH) (hb1:=hb1) (U:=U) (V:=V) (hU:=hU) (hV:=hV)
  (P:=P) (Λ:=Λ) (κ:=κ) (hκ:=hκ) (hκP:=hκP) (I0:=I0) (I1:=I1) θ

def lower (p : ℝ≥0×Ω) : ℝ:=ProfileVariance.lowerConstant*P.lower*(NativeGammaClock.age v b p)^(1/2:ℝ)
def sharp (A β : ℝ) (j : ℕ) (p : ℝ≥0×Ω) : ℝ:=
  A*ScalarHeatBandEnvelope.constant β 0*CompactMollifier.radius (j+1)^(β-1)*
    ScalarHeatBandEnvelope.decay (CompactMollifier.radius (j+1)) (lower (v:=v) (b:=b) (P:=P) p) ((3-β)/2)

theorem lower_pos (p : ℝ≥0×Ω) : 0<lower (v:=v) (b:=b) (P:=P) p:=
  mul_pos (mul_pos ProfileVariance.lowerConstant_pos P.lower_pos)
    (Real.rpow_pos_of_pos (NativeGammaClock.age_pos v b p) _)

include hb1 in
theorem variance_lower (θ : ℝ) (p : ℝ≥0×Ω) (hp : p∈NativeGammaClock.window v b) (x : HeatCircle) :
    lower (v:=v) (b:=b) (P:=P) p≤(Variance θ) (p,x) := by
  have he:=NativeCanonicalVarianceField.lower P Λ θ v b u d p.1 hp.1 hp.2 hb1 p.2 x
  simpa only [lower,NativeGammaClock.age,ite_eq_left hp,NativeJointGammaFields.variance,Prod.eta] using he

theorem sharp_nonneg {A : ℝ} (hA : 0≤A) (β : ℝ) (j : ℕ) (p : ℝ≥0×Ω) :
    0≤sharp (v:=v) (b:=b) (P:=P) A β j p :=
  mul_nonneg (mul_nonneg (mul_nonneg hA (ScalarHeatBandEnvelope.constant_nonneg β 0))
    (Real.rpow_nonneg (CompactMollifier.radius_pos _).le _))
    (le_min zero_le_one (Real.rpow_nonneg (div_nonneg (lower_pos (v:=v) (b:=b) (P:=P) p).le (sq_nonneg _)) _))

/-- Every actual complete-Gamma gradient has the sharp future Gaussian
decay, with its own canonical covariance and its actual current/frozen
mean. Predictability and the lower reserve have both been discharged. -/
theorem rows_bound (hb0 : 0<b) (hnull : NullCompleteFiltration.ContainsNullSets 𝓕 μ)
    (B0 B1 : ℝ≥0) (hBDG0 : StandardTerminalBDG16 I0 B0) (hBDG1 : StandardTerminalBDG16 I1 B1)
    {a : ℝ→ℝ} (ha : BoundedSmooth a) {A β : ℝ} (hA : 0≤A) (hβ : 0≤β) (hβ1 : β≤1)
    (hh : ∀ x y,|a x-a y|≤A*|x-y|^β) (j : ℕ)
    (p : ℝ≥0×Ω) (hp : p∈NativeGammaClock.window v b) (i : Fin 6) :
    ∀ᵐ x∂AddCircle.haarAddCircle,
      ‖NativeRandomRows.nativeRow
        (NativeJointGammaFields.fields (𝓕:=𝓕) (μ:=μ) (H:=H) (v:=v) (b:=b) (hbH:=hbH) (hb1:=hb1)
          (U:=U) (V:=V) (hU:=hU) (hV:=hV) (P:=P) (Λ:=Λ) (κ:=κ) (hκ:=hκ) (hκP:=hκP)
          (I0:=I0) (I1:=I1) a j i) p x‖≤sharp (v:=v) (b:=b) (P:=P) A β j p := by
  letI : MeasurableSpace (ℝ≥0×Ω):=𝓕.predictable
  have hσ0:=NativeJointGammaFields.variance_predictable (𝓕:=𝓕) (v:=v) (b:=b) (U:=U) (V:=V)
    (hU:=hU) (hV:=hV) (P:=P) (Λ:=Λ) 0
  have hσ1:=NativeJointGammaFields.variance_predictable (𝓕:=𝓕) (v:=v) (b:=b) (U:=U) (V:=V)
    (hU:=hU) (hV:=hV) (P:=P) (Λ:=Λ) 1
  have hz0:=NativeJointGammaFields.current_predictable (𝓕:=𝓕) (v:=v) (b:=b) (U:=U) (V:=V) (hU:=hU) (hV:=hV) (Λ:=Λ) 0
  have hz1:=NativeJointGammaFields.current_predictable (𝓕:=𝓕) (v:=v) (b:=b) (U:=U) (V:=V) (hU:=hU) (hV:=hV) (Λ:=Λ) 1
  have hm0:=NativeJointGammaFields.reference_predictable (𝓕:=𝓕) (μ:=μ) (H:=H) (v:=v) (b:=b) (hbH:=hbH) (hb1:=hb1)
    (U:=U) (V:=V) (hU:=hU) (hV:=hV) (P:=P) (Λ:=Λ) (κ:=κ) (hκ:=hκ) (hκP:=hκP) (I0:=I0) (I1:=I1)
    hb0 hnull B0 B1 hBDG0 hBDG1 0
  have hm1:=NativeJointGammaFields.reference_predictable (𝓕:=𝓕) (μ:=μ) (H:=H) (v:=v) (b:=b) (hbH:=hbH) (hb1:=hb1)
    (U:=U) (V:=V) (hU:=hU) (hV:=hV) (P:=P) (Λ:=Λ) (κ:=κ) (hκ:=hκ) (hκP:=hκP) (I0:=I0) (I1:=I1)
    hb0 hnull B0 B1 hBDG0 hBDG1 1
  have hs:=ScalarHeatPairedMultipliers.bound ha hA hβ hβ1 (lower_pos (v:=v) (b:=b) (P:=P) p) hh j
    hσ0 hσ1 hz0 hz1 hm0 hm1 p (ae_of_all _ (variance_lower (v:=v) (b:=b) (hb1:=hb1) (U:=U) (V:=V) (P:=P) (Λ:=Λ) 0 p hp))
    (ae_of_all _ (variance_lower (v:=v) (b:=b) (hb1:=hb1) (U:=U) (V:=V) (P:=P) (Λ:=Λ) 1 p hp)) i
  simpa only [NativeJointGammaFields.fields,ScalarHeatSixFields.nativeRow,sharp] using hs

end SHE.NativeJointGammaSharp

