module

public import SHE.MixedNativeFirstEndpointObservation
public import SHE.MixedNativeDifferenceEndpointObservation
public import SHE.NativeScalarProductLinear
public import SHE.RescaledRowsCoherence
public import SHE.JointGammaEndpointValues
public import SHE.JointGammaOriginalIto
public import SHE.JointGammaNativeInput
public import SHE.JointGammaEndpointIto
public import SHE.JointGammaNativeRaw
public import SHE.JointGammaNativeNoise
public import SHE.NativeGammaDamping
public import SHE.JointGammaNativeGradients
public import SHE.JointGammaNativeRows
public import SHE.JointGammaScalarNoise
public import SHE.NativeJointPhysicalGammaAlgebra
public import SHE.JointGammaNativeCurrentTime
public import SHE.JointGammaNativeReferenceTime
public import SHE.NativeCanonicalVarianceIdentity
public import SHE.NativeJointGammaFields
public import SHE.JointGammaCurrentTime
public import SHE.NativeJointCurrentSections
public import SHE.JointGammaCurrentIdentity
public import SHE.NativeJointGammaCurrent
public import SHE.JointInterpolationFields
public import SHE.ScalarCovarianceTailScale
public import SHE.NativeScalarProductAlgebra
public import SHE.JointGammaAffine
public import SHE.FirstGammaEndpointPhysical
public import SHE.FirstGammaEndpointCoherence
public import SHE.FirstGammaCurrentIdentity
public import SHE.FirstGammaEndpointConstruction
public import SHE.FirstGammaConstruction
public import SHE.FirstGammaRows
public import SHE.RescaledRowsCoherence
public import SHE.FiniteSpliceStopCoherence
public import SHE.FirstGammaEndpointRows
public import SHE.SingularReferenceSplice
public import SHE.FullHorizonEndpointVersion
public import SHE.SingularInputBounds
public import SHE.MixedNativeFrozenPrefixIto
public import SHE.FirstGammaAffine
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

namespace SHE.JointGammaEndpointCurrentNative
open MeasureTheory GaussianIncrement NativeHeatObservation NativeObservationNaturality
open FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation PredictableL2
open scoped NNReal ENNReal
local instance jointGammaOriginalIto_realSigma : MeasurableSpace RealL2 := borel _
local instance jointGammaOriginalIto_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance jointGammaOriginalIto_circleSigma : MeasurableSpace CircleL2 := borel _
local instance jointGammaOriginalIto_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩
local instance jointGammaOriginalIto_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance jointGammaOriginalIto_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance jointGammaOriginalIto_blockSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance jointGammaOriginalIto_blockBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
variable {Ω : Type*} [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
variable (Λ κ : ℝ) (hκ : 0<κ) {aU aV : ℝ→ℝ} (haU : Measurable aU) (haV : Measurable aV) {ell M : ℝ}
variable (hell : 0<ell) (hbU : ∀ z,ell≤aU z ∧ aU z≤M) (hbV : ∀ z,ell≤aV z ∧ aV z≤M)
variable (I₀ I₁ : StandardTerminalIto (C := RealHaarIntegrand.Columns) (E := RealL2) 𝓕 μ H)
variable (u₀ v₀ : RealL2)
variable (S : MixedNativeAdditiveResidualPair.Solution 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀)
variable {n : ℕ} (Z : Fin n→WordRecursion.Observation)



variable (J : StandardTerminalIto (C:=Both RealHaarInput) (E:=ℝ) 𝓕 μ H)
variable (P : CanonicalCovariance.ProfileParameters) (hκP : κ<P.lower)
variable (hΛ : 0≤Λ) (v b : ℝ≥0) (htarget : ∀ i,(b:ℝ)≤(Z i).target) (hbH : b≤H)


local instance jointGammaOriginalIto_period : Fact (0<2*Real.pi):=⟨by positivity⟩
local instance jointGammaOriginalIto_unit : Fact (0<(1:ℝ)):=⟨zero_lt_one⟩
local instance jointGammaOriginalIto_unitSecond : SecondCountableTopology CircleHeat.CircleL2:=
  (_root_.fourierBasis (T:=(1:ℝ))).repr.toHomeomorph.secondCountableTopology
local instance jointGammaOriginalIto_realSecond : SecondCountableTopology RealL2:=
  FiniteHaar.realCircleIdentification.toHomeomorph.secondCountableTopology
variable (hH : (H:ℝ)≤1) (B : ℝ≥0) (hBDG : StandardTerminalBDG16 J B)
variable (hIJ₀ : StandardScalarNaturality I₀ (leftIntegral 𝓕 μ H J))
variable (hIJ₁ : StandardScalarNaturality I₁ (rightIntegral 𝓕 μ H J))
attribute [local irreducible] FirstGammaEndpointConstruction.value NativeJointGammaCurrent.state
attribute [local irreducible] JointGammaNativeInput.input

variable (hvb:v≤b)
local notation "hEndOne"=>(show (b:ℝ)≤(H:ℝ) by exact_mod_cast hbH).trans hH
local notation "SU"=>Function.uncurry S.first
local notation "SV"=>Function.uncurry S.second
local notation "OldU"=>S.first v
local notation "OldD"=>(fun ω=>S.second v ω-S.first v ω)
local notation "Past"=>MixedNativeFrozenPrefixIto.data 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S v
local notation "Zx" =>(fun x:HeatCircle=>ScalarCovarianceTailScale.observation b x)
local notation "Yx" =>(fun (θ:ℝ) (x:HeatCircle)=>FirstGammaEndpointConstruction.value 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
  (Zx x) J P hκP hΛ v b (fun _=>le_rfl) hbH θ)
local notation "Window" =>(fun (θ:ℝ) (x:HeatCircle) (ω:Ω)=>ControlledReferenceWindows.window P Λ θ v (Zx x) b
  (by exact_mod_cast hvb) (fun _=>le_rfl) (Past ω))
local notation "Var" θ=>NativeJointGammaFields.variance (v:=v) (b:=b) (U:=SU) (V:=SV) (P:=P) (Λ:=Λ) θ
local notation "Cur" θ=>NativeJointGammaFields.current (v:=v) (b:=b) (U:=SU) (V:=SV) (Λ:=Λ) θ
local notation "Ref" θ=>NativeJointGammaFields.reference (𝓕:=𝓕) (μ:=μ) (H:=H) (v:=v) (b:=b)
  (hbH:=hbH) (hb1:=hEndOne) (U:=SU) (V:=SV) (hU:=S.first_predictable) (hV:=S.second_predictable)
  (P:=P) (Λ:=Λ) (κ:=κ) (hκ:=hκ) (hκP:=hκP) (I0:=I₀) (I1:=I₁) θ

local notation "First"=>MixedNativeFirstEndpointObservation.rows 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S b hbH
local notation "Diff"=>MixedNativeDifferenceEndpointObservation.rows 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S b hbH hΛ
local notation "ED"=>(fun ω=>Real.exp (Λ*(b:ℝ)) • (S.second b ω-S.first b ω))

include B hBDG hH in
/-- Exact original-input endpoint coordinates of the finite extended
martingale. All stopped rows keep the original full target. -/
theorem coordinates (hb0:0<b)(θ:ℝ)(x:HeatCircle):
    ∀ᵐω∂μ,
      FirstGammaAffine.currentU 1 (Yx θ x (b,ω)) 0=
        functional (b:ℝ) x u₀+J.integral (First x 0) ω ∧
      FirstGammaAffine.currentD 1 (Yx θ x (b,ω)) 0=
        functional (b:ℝ) x (v₀-u₀)+J.integral (Diff x 0) ω:=by
  have hp:=FirstGammaEndpointConstruction.integral_representation 𝓕 μ H Λ κ hκ haU haV hell hbU hbV
    I₀ I₁ u₀ v₀ S (Zx x) J P hκP hΛ v b (fun _=>le_rfl) hbH θ hb0 hEndOne B hBDG b
  have hU:StoppedItoInputs.stop 𝓕 μ H b
      (FirstGammaEndpointRows.actual 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S (Zx x) hΛ b
        (fun _=>le_rfl) hbH (Fin.castAdd 1 0))=First x 0:=by
    simp only [FirstGammaEndpointRows.actual,Fin.append_left,TwoChannelItoRows.stop_block,
      FirstGammaEndpointRows.additive,FirstGammaEndpointRows.first,ScalarCovarianceTailScale.observation]
    rw [FullHorizonEndpointStop.self,FullHorizonEndpointStop.self]
    simp only [MixedNativeFirstEndpointObservation.rows,max_self,add_zero]
  have hD:StoppedItoInputs.stop 𝓕 μ H b
      (FirstGammaEndpointRows.actual 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S (Zx x) hΛ b
        (fun _=>le_rfl) hbH (Fin.natAdd 1 0))=Diff x 0:=by
    simp only [FirstGammaEndpointRows.actual,Fin.append_right]
    rw [RescaledRowsCoherence.stop_rescaled 𝓕 μ H hΛ b b le_rfl]
    simp only [FirstGammaEndpointRows.first,FirstGammaEndpointRows.second,ScalarCovarianceTailScale.observation]
    rw [FullHorizonEndpointStop.self,FullHorizonEndpointStop.self]
    simp only [MixedNativeDifferenceEndpointObservation.rows,MixedNativeDifferenceEndpointObservation.firstRow,
      MixedNativeDifferenceEndpointObservation.secondRow,max_self,add_zero]
  filter_upwards [hp] with ω hp
  constructor
  · rw [hp]
    simp only [FirstGammaAffine.currentU,ContinuousLinearMap.comp_apply,ObservationBlockMaps.first_apply,
      FiniteComparisonTest.left_apply,StandardFiniteIto.vectorIntegral,WithLp.ofLp_toLp,
      FirstGammaEndpointConstruction.rows,SingularReferenceSplice.rows,FiniteReferenceSplice.jointRows,
      Fin.append_left,StoppedInputAlgebra.stop_stop,min_self,FiniteReferenceSplice.jointInitial,
      MixedNativePairExtendedMartingale.initial,ScalarCovarianceTailScale.observation]
    rw [hU]
  · rw [hp]
    simp only [FirstGammaAffine.currentD,ContinuousLinearMap.comp_apply,ObservationBlockMaps.second_apply,
      FiniteComparisonTest.left_apply,StandardFiniteIto.vectorIntegral,WithLp.ofLp_toLp,
      FirstGammaEndpointConstruction.rows,SingularReferenceSplice.rows,FiniteReferenceSplice.jointRows,
      Fin.append_left,Fin.append_right,StoppedInputAlgebra.stop_stop,min_self,FiniteReferenceSplice.jointInitial,
      MixedNativePairExtendedMartingale.initial,ScalarCovarianceTailScale.observation]
    rw [hD]

include B hBDG hH hIJ₀ hIJ₁ in
/-- Literal joint current at the genuine singular terminal endpoint
is the jointly measurable native field of U_b+θ(V_b−U_b). -/
theorem current_eq_field (hb0:0<b)(θ:ℝ):
    ∀ᵐx:HeatCircle∂AddCircle.haarAddCircle,∀ᵐω∂μ,
      JointGammaAffine.current 1 Λ θ (fun _=>(b:ℝ)) (Yx θ x (b,ω)) 0=
        PredictableScalarField.nativeField
          (NativeJointGammaCurrent.state SU SV Λ θ b) ((b,ω),x):=by
  have hu:Measurable (S.first b):=(S.first_predictable.mono (predictable_le_product 𝓕)).measurable.comp
    ((measurable_const (a:=b)).prodMk (measurable_id : Measurable (id:Ω→Ω)))
  have hd:Measurable ED:=(((S.second_predictable.sub S.first_predictable).mono (predictable_le_product 𝓕)).measurable.comp
    ((measurable_const (a:=b)).prodMk (measurable_id : Measurable (id:Ω→Ω)))).const_smul (Real.exp (Λ*(b:ℝ)))
  have hstate(ω:Ω):NativeJointGammaCurrent.state SU SV Λ θ b (b,ω)=
      S.first b ω+(θ*Real.exp (-Λ*(b:ℝ))) • ED ω:=by
    have he:Real.exp (-Λ*(b:ℝ))*Real.exp (Λ*(b:ℝ))=1:=by
      rw [←Real.exp_add];simp
    simp only [NativeJointGammaCurrent.state,sub_self,mul_zero,neg_zero,Real.exp_zero,one_smul,
      NativeHeatObservation.heat,zero_div,RealHeat.realHeat_zero,ContinuousLinearMap.id_apply,
      smul_smul,mul_assoc,he,mul_one,Function.uncurry_apply_pair]
  have h0:=MixedNativeFirstEndpointObservation.observation 𝓕 μ H Λ κ hκ haU haV hell hbU hbV
    I₀ I₁ u₀ v₀ S J hIJ₀ hIJ₁ b hbH hb0
  have h1:=MixedNativeDifferenceEndpointObservation.observation 𝓕 μ H Λ κ hκ haU haV hell hbU hbV
    I₀ I₁ u₀ v₀ S J hIJ₀ hIJ₁ b hbH hΛ hb0
  have hl:=NativeScalarProductLinear.add_smul_ae μ (θ*Real.exp (-Λ*(b:ℝ))) (S.first b) ED hu hd
  filter_upwards [h0,h1,hl] with x h0 h1 hl
  filter_upwards [h0,h1,hl,coordinates 𝓕 μ H Λ κ hκ haU haV hell hbU hbV
    I₀ I₁ u₀ v₀ S J P hκP hΛ v b hbH hH B hBDG hb0 θ x] with ω h0 h1 hl hc
  rw [JointGammaAffine.current_apply,hc.1,hc.2]
  change _=PredictableScalarField.nativeField
    (fun ω=>NativeJointGammaCurrent.state SU SV Λ θ b (b,ω)) (ω,x)
  rw [NativeScalarFieldAlgebra.congr (fun ω=>NativeJointGammaCurrent.state SU SV Λ θ b (b,ω))
    (fun ω=>S.first b ω+(θ*Real.exp (-Λ*(b:ℝ))) • ED ω) ω (hstate ω) x,hl,h0,h1]

end SHE.JointGammaEndpointCurrentNative
