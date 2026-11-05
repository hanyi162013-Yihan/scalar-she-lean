module

public import SHE.MixedNativeVarianceGammaTime
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

namespace SHE.MixedNativeJointRowFields
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

def fields (a:ℝ→ℝ) (j:ℕ):Fin 6→(ℝ≥0×Ω)×HeatCircle→ℂ:=
  NativeJointGammaFields.fields (𝓕:=𝓕) (μ:=μ) (H:=H) (v:=v) (b:=b) (hbH:=hbH) (hb1:=Bbound)
    (U:=UU) (V:=VV) (hU:=S.first_predictable) (hV:=S.second_predictable) (P:=P) (Λ:=Λ) (κ:=κ)
    (hκ:=hκ) (hκP:=hκP) (I0:=I₀) (I1:=I₁) a j
local notation "Fields"=>fields 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P hκP v b hbH hH

include hvb in
theorem fields_measurable (hnull:NullCompleteFiltration.ContainsNullSets 𝓕 μ)
    (B0 B1:ℝ≥0) (hBDG0:StandardTerminalBDG16 I₀ B0) (hBDG1:StandardTerminalBDG16 I₁ B1)
    (a:ℝ→ℝ) (ha:SmoothCylinders.BoundedSmooth a) (j:ℕ) (i:Fin 6):
    Measurable (Fields a j i):=by
  have hb0:0<b:=(show (0:ℝ≥0)≤v from zero_le).trans_lt hvb
  have hp:=NativeJointGammaFields.fields_predictable (𝓕:=𝓕) (μ:=μ) (H:=H) (v:=v) (b:=b) (hbH:=hbH) (hb1:=Bbound)
    (U:=UU) (V:=VV) (hU:=S.first_predictable) (hV:=S.second_predictable) (P:=P) (Λ:=Λ) (κ:=κ)
    (hκ:=hκ) (hκP:=hκP) (I0:=I₀) (I1:=I₁) hb0 hnull B0 B1 hBDG0 hBDG1 a ha j i
  have hf:@Measurable ((ℝ≥0×Ω)×HeatCircle) (ℝ≥0×Ω) inferInstance 𝓕.predictable Prod.fst:=by
    intro A hA
    exact measurable_fst ((predictable_le_product 𝓕) A hA)
  exact hp.comp (hf.prodMk measurable_snd)

theorem fields_bound {a:ℝ→ℝ} (ha:SmoothCylinders.BoundedSmooth a) {A:ℝ} (hA:0≤A)
    (hh:∀x y,|a x-a y|≤A*|x-y|^P.exponent) (j:ℕ) (i:Fin 6) (p:ℝ≥0×Ω) (x:HeatCircle):
    ‖Fields a j i (p,x)‖≤ScalarHeatSingleMultiplier.cap A P.exponent j:=
  NativeJointGammaFields.fields_bound (𝓕:=𝓕) (μ:=μ) (H:=H) (v:=v) (b:=b) (hbH:=hbH) (hb1:=Bbound)
    (U:=UU) (V:=VV) (hU:=S.first_predictable) (hV:=S.second_predictable) (P:=P) (Λ:=Λ) (κ:=κ)
    (hκ:=hκ) (hκP:=hκP) (I0:=I₀) (I1:=I₁) ha hA P.exponent_pos.le P.exponent_le_one hh j i p x

theorem clocks (t:ℝ) (ht:t∈Set.Ioo (0:ℝ) ((b:ℝ)-(v:ℝ))):
    (((b:ℝ)-t).toNNReal:ℝ)=(b:ℝ)-t ∧ v<((b:ℝ)-t).toNNReal ∧ ((b:ℝ)-t).toNNReal<b:=by
  have h0:0≤(b:ℝ)-t:=by linarith [v.coe_nonneg,ht.2]
  have he:=Real.coe_toNNReal _ h0
  refine ⟨he,?_,?_⟩
  · exact_mod_cast (show (v:ℝ)<(((b:ℝ)-t).toNNReal:ℝ) by rw [he];linarith [ht.2])
  · exact_mod_cast (show (((b:ℝ)-t).toNNReal:ℝ)<(b:ℝ) by rw [he];linarith [ht.1])

/-- Literal held-past original covariance equals the true remaining
variance used by the sharp analytic time theorem, on the open window. -/
theorem variance_age_eq (ξ t:ℝ) (ht:t∈Set.Ioo (0:ℝ) ((b:ℝ)-(v:ℝ))) (z:Ω×HeatCircle):
    NativeJointGammaFields.variance (v:=v) (b:=b) (U:=UU) (V:=VV) (P:=P) (Λ:=Λ) ξ
      ((((b:ℝ)-t).toNNReal,z.1),z.2)=
    MixedNativeVarianceGammaTime.variance 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P v b ξ (t,z):=by
  rcases clocks v b t ht with ⟨hq,hvq,hqb⟩
  rw [NativeJointGammaFields.variance,NativeCanonicalVarianceField.field_eq P Λ ξ v b _ _
    ((b:ℝ)-t).toNNReal hvq hqb.le z.1 z.2]
  dsimp only [MixedNativeVarianceGammaTime.variance,ControlledVarianceGammaTime.variance,ControlledScalarCovarianceTailEnergy.field]
  rw [min_eq_left (by linarith [ht.1]:(b:ℝ)-t≤(b:ℝ)),hq]
  rfl

end SHE.MixedNativeJointRowFields
