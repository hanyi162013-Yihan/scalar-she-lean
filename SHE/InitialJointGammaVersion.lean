module
public import SHE.InitialJointGammaSharpEnergy
public import SHE.InitialJointGammaNoise
public import SHE.MixedNativeHigherInitialOutput
public import SHE.InitialJointGammaBudget
public import SHE.MixedNativeJointGammaOutput
public import SHE.InitialJointCurrentBudget
public import SHE.InitialSignedGammaRows
public import SHE.MixedMovingEnergy
public import SHE.InitialJointGammaZeroBudgets
public import SHE.MixedNativeJointGammaPhysicalBudget
public import SHE.InitialNativeColumnEnergy
public import SHE.MixedNativeJointRowBudgets
public import SHE.MixedNativeFrozenFactorPositive
public import SHE.JointGammaFrozenCanonical
public import SHE.JointGammaRootHilbertPair
public import SHE.FirstGammaTerminalReferenceEnergy
public import SHE.JointGammaRootScalarPair
public import SHE.JointGammaOriginalHilbert
public import SHE.NativeBesselDifferenceIdentity
public import SHE.NativeBesselFiniteIdentity
public import SHE.MixedNativePairedRootZero
public import SHE.JointGammaRootRecursion
public import SHE.ControlledScalarReference
public import SHE.JointGammaActualEndpointPair
public import SHE.JointGammaFirstPairRecursion
public import SHE.JointGammaOriginalRegrouping

public import SHE.JointGammaEndpointCurrentNative
public import SHE.FirstGammaEndpointReferenceNative
public import SHE.NativeJointCurrentEndpoint
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
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2300000

namespace SHE.InitialJointGammaVersion
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
variable {Ω : Type} [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
variable (Λ κ : ℝ) (hκ : 0<κ) {aU aV : ℝ→ℝ} (haU : Measurable aU) (haV : Measurable aV) {ell M : ℝ}
variable (hell : 0<ell) (hbU : ∀ z,ell≤aU z ∧ aU z≤M) (hbV : ∀ z,ell≤aV z ∧ aV z≤M)
variable (I₀ I₁ : StandardTerminalIto (C := RealHaarIntegrand.Columns) (E := RealL2) 𝓕 μ H)
variable (u₀ : RealL2)
variable (S : MixedNativeAdditiveResidualPair.Solution 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀)
variable (J:StandardTerminalIto (C:=Both RealHaarInput) (E:=ℝ) 𝓕 μ H)
variable (P:CanonicalCovariance.ProfileParameters) (hκP:κ<P.lower) (hΛ:0≤Λ) (b:ℝ≥0) (hbH:b≤H) (hH:(H:ℝ)≤1)
variable (B:ℝ≥0) (hBDG:StandardTerminalBDG16 J B)
variable (hIJ₀:StandardScalarNaturality I₀ (leftIntegral 𝓕 μ H J))
variable (hIJ₁:StandardScalarNaturality I₁ (rightIntegral 𝓕 μ H J))
variable  (hnull:NullCompleteFiltration.ContainsNullSets 𝓕 μ)
variable (B0 B1:ℝ≥0) (hBDG0:StandardTerminalBDG16 I₀ B0) (hBDG1:StandardTerminalBDG16 I₁ B1)
variable (hsmallL2:ProfileStability.memoryConstant P.lower P.holder P.exponent*
  ProfileVolterra.powerConstant ((P.exponent-1)/4)*P.horizon^(P.exponent/4)≤1/2)
variable (Bpast:ℝ≥0) (hBDGpast:StandardTerminalBDGPower 2 J Bpast)
variable (hlocal:StandardTerminalPastLocality I₁) (Bnext:ℝ≥0) (hBDGnext:StandardTerminalBDGPower 1 I₁ Bnext)
local instance : Fact (0<2*Real.pi):=⟨by positivity⟩
variable {a:ℝ→ℝ}(ha:SmoothCylinders.BoundedSmooth a){A ρ:ℝ}(hA:0≤A)
variable (hρ:0<ρ)(hρhalf:ρ<1/2)(hholder:∀x y,|a x-a y|≤A*|x-y|^P.exponent)(j:ℕ)(hL:1≤Λ)
local notation "Lower"=>MixedNativeGammaEnergy.commonLower (ell:=ell) (P:=P) (κ:=κ)
local notation "Upper"=>MixedNativeGammaEnergy.commonUpper (M:=M) (P:=P) (κ:=κ)
local notation "hm"=>MixedNativeGammaEnergy.commonLower_pos (ell:=ell) (P:=P) (κ:=κ) (hell:=hell) (hκP:=hκP)
local notation "Trace"=>NativeConvexGammaUniform.constant Lower Upper hm hρ hρhalf
local notation "Ksum"=>(κ+Upper)*(1+2*HeatTrace.fractionalGaussianIntegral ρ)

variable (h:ℝ≥0)(hhH:h≤H)
local notation "UU"=>Function.uncurry S.first
local notation "VV"=>Function.uncurry S.second
local notation "Global"=>MixedMovingEnergy.globalEnergy 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
local notation "Neg"=>MixedActualEnergyBridge.negativeEnergy 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S ρ

local notation "Radius"=>CompactMollifier.radius (j+1)
local notation "Cgamma"=>JointGammaConstants.nativeConstant P A κ ell M hell hκP hρ hρhalf Bnext
local notation "Output"=>InitialJointGammaEnergy.output
  (𝓕:=𝓕) (μ:=μ) (H:=H) (Λ:=Λ) (κ:=κ) (hκ:=hκ) (haU:=haU) (haV:=haV) (hell:=hell) (hbU:=hbU) (hbV:=hbV)
  (I₀:=I₀) (I₁:=I₁) (u₀:=u₀) (S:=S) (P:=P) (hκP:=hκP) (hH:=hH) (hnull:=hnull)
  (B0:=B0) (B1:=B1) (hBDG0:=hBDG0) (hBDG1:=hBDG1) (ha:=ha) (hA:=hA) (hρ:=hρ) (hρhalf:=hρhalf)
  (hholder:=hholder) (j:=j) (hL:=hL) (h:=h) (hhH:=hhH)
local notation "Root"=>(fun z:WordRecursion.State 1=>ScalarHeatBands.band a (j+1) (z 0))
local notation "RootSmooth"=>(ScalarHeatBands.band_boundedSmooth ha (j+1)).comp_right (EuclideanSpace.proj (0:Fin 1))
local notation "RootFamily"=>(fun _:HeatCircle=>Root)
local notation "RootUniform"=>UniformSmooth.UniformBoundedSmooth.fixed (P:=HeatCircle) RootSmooth
local notation "RootMeasurable"=>(RootSmooth).smooth.continuous.measurable.comp
  (measurable_snd:Measurable (Prod.snd:HeatCircle×WordRecursion.State 1→WordRecursion.State 1))
variable (haP:SmoothCylinders.BoundedSmooth P.coefficient)
variable (hJ:StandardFiniteIto.Universal 𝓕 μ H J)(hAs:SmoothCylinders.BoundedSmooth (fun z=>κ+aV z))
local notation "Higher"=>MixedNativeHigherInitialOutput.output
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h RootFamily RootUniform RootMeasurable
  J hIJ₀ hIJ₁ hnull hJ hAs hL hρ.le 0

include hIJ₀ hIJ₁ hsmallL2 hBDGpast hBDG hlocal hBDGnext haP hJ hAs in
/-- Genuine Borel initial Gamma output, identified with the same
original two Ito channels and obeying the sharp initial frequency cap. -/
theorem exists_output(hh:0<h)(hspan:(h:ℝ)≤P.horizon)
    (hsmall:ProfileStability.memoryConstant P.lower P.holder P.exponent*
      ProfileVolterra.powerConstant ((P.exponent-2)/4)*P.horizon^(P.exponent/4)≤1/2)
    (hActual:P.coefficient=(fun z=>κ+aV z))
    (hspanF:(h:ℝ)≤NativeUniversalConstants.rowHorizon 1)
    (hspanC:(h:ℝ)≤4*Real.pi^2*NativeUniversalConstants.currentHorizon.{0} 1 (by omega))
    (hspanS:(h:ℝ)≤UniformFutureProfileScores.horizon 1)
    (hlocalJ:StandardTerminalPastLocality J)(hFubini:StandardItoParameterFubini J)
    (Bg B4 B8:ℝ≥0)(hBDGg:StandardTerminalBDGPower 1 J Bg)
    (hBDG4:StandardTerminalBDGPower 4 J B4)(hBDG8:StandardTerminalBDGPower 8 J B8):
    ∃Y:ℝ≥0×Ω→CircleL2,Measurable Y ∧
      (∀ᵐt∂timeMeasure h,(fun ω=>Y (t,ω))=ᵐ[μ] (fun ω=>Output ((t:ℝ),ω))) ∧
      (∫⁻t,∫⁻ω,ENNReal.ofReal (‖Y (t,ω)‖^2) ∂μ ∂timeMeasure h)≤
        ENNReal.ofReal (Cgamma*(Radius^(2*P.exponent)*(Neg).toReal+
          Radius^(2*P.exponent+4*ρ)*((h:ℝ)^((P.exponent-1)/2)*Global+min 1 (Global/Radius^2)))):=by
  classical
  have hsection(t:ℝ≥0):∀ᵐω∂μ,Higher (t,ω)= -Output ((t:ℝ),ω):=by
    by_cases ht:0<t∧t≤h
    · have htH:t≤H:=ht.2.trans hhH
      have hn:=InitialJointGammaNoise.higher_zero_eq_neg_original
        (𝓕:=𝓕) (μ:=μ) (H:=H) (Λ:=Λ) (κ:=κ) (hκ:=hκ) (haU:=haU) (haV:=haV)
        (hell:=hell) (hbU:=hbU) (hbV:=hbV) (I₀:=I₀) (I₁:=I₁) (u₀:=u₀) (S:=S)
        (J:=J) (P:=P) (hκP:=hκP) (hΛ:=zero_le_one.trans hL) (v:=0) (b:=t)
        (hbH:=htH) (hH:=hH) (B:=B) (hBDG:=hBDG) (hIJ₀:=hIJ₀) (hIJ₁:=hIJ₁) (hvb:=bot_le)
        (ha:=ha) (j:=j) (hb0:=ht.1) (hnull:=hnull) (B0:=B0) (B1:=B1) (hBDG0:=hBDG0) (hBDG1:=hBDG1)
        (hA:=hA) (hβ:=P.exponent_pos.le) (hβ1:=P.exponent_le_one) (hh:=hholder)
        (hsmall:=hsmall) (hAs:=hAs) (hJ:=hJ) (hL:=hL) (hρ:=hρ) (hρhalf:=hρhalf)
        (hsmallL2:=hsmallL2) (Bpast:=Bpast) (hBDGpast:=hBDGpast) (hlocalI:=hlocal) (Bnext:=Bnext) (hBDGnext:=hBDGnext)
        rfl hActual (le_trans (by exact_mod_cast ht.2) hspan) (le_trans (by exact_mod_cast ht.2) hspanS)
        hlocalJ hFubini Bg B8 hBDGg hBDG8
      have hclip:InitialNativeKernelFibre.terminal Λ u₀ P haP h
          (InitialRetainedTriangleEnergy.clippedTime h (t:ℝ))=t:=by
        ext
        exact ClippedCovariance.clip_eq ⟨t.property,by exact_mod_cast ht.2⟩
      filter_upwards [hn] with ω hω
      simp only [MixedNativeHigherInitialOutput.output,if_pos ht,MixedNativeHigherInitialEnergy.output,
        hclip,InitialJointGammaEnergy.output,Real.toNNReal_coe,
        dif_pos (show 0<(t:ℝ)∧(t:ℝ)≤h by exact_mod_cast ht)]
      exact hω
    · filter_upwards [] with ω
      have ht':¬(0<(t:ℝ)∧(t:ℝ)≤h):=by exact_mod_cast ht
      simp only [MixedNativeHigherInitialOutput.output,if_neg ht,InitialJointGammaEnergy.output,dif_neg ht',neg_zero]
  have hmass:(∫⁻t,∫⁻ω,ENNReal.ofReal (‖Higher (t,ω)‖^2) ∂μ ∂timeMeasure h)=
      ∫⁻T in Set.Ioc (0:ℝ) (h:ℝ),InitialJointGammaEnergy.energy
        (𝓕:=𝓕) (μ:=μ) (H:=H) (Λ:=Λ) (κ:=κ) (hκ:=hκ) (haU:=haU) (haV:=haV)
        (hell:=hell) (hbU:=hbU) (hbV:=hbV) (I₀:=I₀) (I₁:=I₁) (u₀:=u₀) (S:=S) (P:=P) (hκP:=hκP)
        (hH:=hH) (hnull:=hnull) (B0:=B0) (B1:=B1) (hBDG0:=hBDG0) (hBDG1:=hBDG1) (ha:=ha)
        (hA:=hA) (hρ:=hρ) (hρhalf:=hρhalf) (hholder:=hholder) (j:=j) (hL:=hL) (h:=h) (hhH:=hhH) T:=by
    calc
      _=∫⁻t,∫⁻ω,ENNReal.ofReal (‖Output ((t:ℝ),ω)‖^2) ∂μ ∂timeMeasure h:=by
        apply lintegral_congr
        intro t
        apply lintegral_congr_ae
        filter_upwards [hsection t] with ω hω
        rw [hω,norm_neg]
      _=_:=by
        rw [timeMeasure_lintegral]
        apply lintegral_congr_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
        simp only [Real.coe_toNNReal _ ht.1.le,InitialJointGammaEnergy.energy]
  have he:=InitialJointGammaSharpEnergy.complete_energy
    (𝓕:=𝓕) (μ:=μ) (H:=H) (Λ:=Λ) (κ:=κ) (hκ:=hκ) (haU:=haU) (haV:=haV) (hell:=hell) (hbU:=hbU) (hbV:=hbV)
    (I₀:=I₀) (I₁:=I₁) (hIJ₀:=hIJ₀) (hIJ₁:=hIJ₁) (u₀:=u₀) (S:=S) (J:=J) (P:=P) (hκP:=hκP) (hH:=hH)
    (hsmallL2:=hsmallL2) (Bpast:=Bpast) (hBDGpast:=hBDGpast) (hnull:=hnull) (B0:=B0) (B1:=B1)
    (hBDG0:=hBDG0) (hBDG1:=hBDG1) (B:=B) (hBDG:=hBDG) (hlocal:=hlocal) (Bnext:=Bnext) (hBDGnext:=hBDGnext)
    (a:=a) (ha:=ha) (A:=A) (ρ:=ρ) (hA:=hA) (hρ:=hρ) (hρhalf:=hρhalf) (hholder:=hholder) (j:=j) (hL:=hL)
    (h:=h) (hhH:=hhH) hh hspan Bg hBDGg
  have hfinite:(∫⁻t,∫⁻ω,ENNReal.ofReal (‖Higher (t,ω)‖^2) ∂μ ∂timeMeasure h)<∞:=
    lt_of_le_of_lt (hmass.trans_le he) ENNReal.ofReal_lt_top
  obtain ⟨C,hC,hCb⟩:=(RootUniform).bounds 0
  have hjet:∀x n,n≤0→∀z,‖iteratedFDeriv ℝ n (RootFamily x) z‖≤C*(1:ℝ)^n:=by
    intro x n hn z
    have he:n=0:=by omega
    subst n
    have hb:=hCb x z
    rw [norm_iteratedFDeriv_zero] at hb ⊢
    change ‖ScalarHeatBands.band a (j+1) (z 0)‖≤C at hb
    simpa only [pow_zero,mul_one] using hb
  obtain ⟨Y,hY,hYa,hYe⟩:=MixedNativeHigherInitialOutput.exists_identified
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h RootFamily RootUniform RootMeasurable
    J hIJ₀ hIJ₁ hnull hJ hAs hActual hlocalJ hL hρ hρhalf hhH hH 0 hsmall hsmallL2
    hspan hspanF hspanC hspanS (fun n hn=>False.elim (Nat.not_lt_zero n hn))
    Bg hBDGg C 1 hC zero_le_one hjet 2 (by norm_num) B4 (by simpa using hBDG4)
    Bpast (by simpa using hBDGpast) (1/2) (by norm_num) (by norm_num) (by norm_num)
    1 0 0 ((1/2-ρ)/2) le_rfl (by norm_num) (by linarith) (by linarith)
    (timeMeasure h) hFubini hfinite
  refine ⟨fun z=> -Y z,hY.neg,?_,?_⟩
  · filter_upwards [hYa] with t ht
    filter_upwards [ht,hsection t] with ω hω hs
    simpa only [hω,hs,neg_neg]
  · simpa only [norm_neg] using hYe.trans_le (hmass.trans_le he)
end SHE.InitialJointGammaVersion
