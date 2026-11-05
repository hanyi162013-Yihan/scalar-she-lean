module
public import SHE.InitialJointGammaVersion
public import SHE.MovingOriginalGammaSharp
public import SHE.NativeOutputTimePatch
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

namespace SHE.FullJointGammaOutput
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

local instance :SecondCountableTopology CircleL2:=
  (_root_.fourierBasis (T:=2*Real.pi)).repr.toHomeomorph.secondCountableTopology
local notation "Width"=>(H:ℝ)-(h:ℝ)
local notation "wNonneg"=>sub_nonneg.mpr (show (h:ℝ)≤(H:ℝ) by exact_mod_cast hhH)
/-- Literal completed-window original Gamma sections. -/
def completed(hh:0<h)(t:ℝ≥0)(ω:Ω):CircleL2:=MovingOriginalGammaHilbert.output
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S P hκP Width (h:ℝ)
  wNonneg (by exact_mod_cast hh) (by ring_nf;exact le_rfl) hH
  hnull B0 B1 hBDG0 hBDG1 ha hA hholder j hL hρ hρhalf (t:ℝ) ω
local notation "Completed"=>completed
  (𝓕:=𝓕) (μ:=μ) (H:=H) (Λ:=Λ) (κ:=κ) (hκ:=hκ) (haU:=haU) (haV:=haV) (hell:=hell) (hbU:=hbU) (hbV:=hbV)
  (I₀:=I₀) (I₁:=I₁) (u₀:=u₀) (S:=S) (P:=P) (hκP:=hκP) (hH:=hH) (hnull:=hnull)
  (B0:=B0) (B1:=B1) (hBDG0:=hBDG0) (hBDG1:=hBDG1) (ha:=ha) (hA:=hA) (hρ:=hρ) (hρhalf:=hρhalf)
  (hholder:=hholder) (j:=j) (hL:=hL) (h:=h) (hhH:=hhH)
/-- The full original physical Gamma, including its true initial
triangle rather than extending completed windows into that triangle. -/
def original(hh:0<h):ℝ≥0×Ω→CircleL2:=NativeOutputTimePatch.field h
  (fun z=>Output ((z.1:ℝ),z.2)) (fun z=>Completed hh z.1 z.2)
local notation "Original"=>original
  (𝓕:=𝓕) (μ:=μ) (H:=H) (Λ:=Λ) (κ:=κ) (hκ:=hκ) (haU:=haU) (haV:=haV) (hell:=hell) (hbU:=hbU) (hbV:=hbV)
  (I₀:=I₀) (I₁:=I₁) (u₀:=u₀) (S:=S) (P:=P) (hκP:=hκP) (hH:=hH) (hnull:=hnull)
  (B0:=B0) (B1:=B1) (hBDG0:=hBDG0) (hBDG1:=hBDG1) (ha:=ha) (hA:=hA) (hρ:=hρ) (hρhalf:=hρhalf)
  (hholder:=hholder) (j:=j) (hL:=hL) (h:=h) (hhH:=hhH)

include hIJ₀ hIJ₁ hsmallL2 hBDGpast hBDG hlocal hBDGnext haP hJ hAs in
/-- One Borel full-time field realizes both original Gamma branches.
Its initial and completed energies add with their exact physical clocks. -/
theorem exists_output(hh:0<h)(hspan:(h:ℝ)≤P.horizon)
    (hsmall:ProfileStability.memoryConstant P.lower P.holder P.exponent*
      ProfileVolterra.powerConstant ((P.exponent-2)/4)*P.horizon^(P.exponent/4)≤1/2)
    (hActual:P.coefficient=(fun z=>κ+aV z))
    (hspanF:(h:ℝ)≤NativeUniversalConstants.rowHorizon 1)
    (hspanC:(h:ℝ)≤4*Real.pi^2*NativeUniversalConstants.currentHorizon.{0} 1 (by omega))
    (hspanS:(h:ℝ)≤UniformFutureProfileScores.horizon 1)
    (hlocalJ:StandardTerminalPastLocality J)(hStopped:StandardItoStoppedParameterFubini J)
    (Bg B4 B8:ℝ≥0)(hBDGg:StandardTerminalBDGPower 1 J Bg)
    (hBDG4:StandardTerminalBDGPower 4 J B4)(hBDG8:StandardTerminalBDGPower 8 J B8):
    ∃G:ℝ≥0×Ω→CircleL2,Measurable G ∧
      (∀ᵐt∂timeMeasure H,(fun ω=>G (t,ω))=ᵐ[μ] (fun ω=>Original hh (t,ω))) ∧
      (∫⁻z,ENNReal.ofReal (‖G z‖^2) ∂energyMeasure μ H)≤
        2*ENNReal.ofReal (Cgamma*(Radius^(2*P.exponent)*(Neg).toReal+
          Radius^(2*P.exponent+4*ρ)*((h:ℝ)^((P.exponent-1)/2)*Global+min 1 (Global/Radius^2)))):=by
  classical
  obtain ⟨I,hI,hIa,hIe⟩:=InitialJointGammaVersion.exists_output
    (𝓕:=𝓕) (μ:=μ) (H:=H) (Λ:=Λ) (κ:=κ) (hκ:=hκ) (haU:=haU) (haV:=haV) (hell:=hell) (hbU:=hbU) (hbV:=hbV)
    (I₀:=I₀) (I₁:=I₁) (hIJ₀:=hIJ₀) (hIJ₁:=hIJ₁) (u₀:=u₀) (S:=S) (J:=J) (P:=P) (hκP:=hκP) (hH:=hH)
    (hsmallL2:=hsmallL2) (Bpast:=Bpast) (hBDGpast:=hBDGpast) (hnull:=hnull) (B0:=B0) (B1:=B1)
    (hBDG0:=hBDG0) (hBDG1:=hBDG1) (B:=B) (hBDG:=hBDG) (hlocal:=hlocal) (Bnext:=Bnext) (hBDGnext:=hBDGnext)
    (a:=a) (ha:=ha) (A:=A) (ρ:=ρ) (hA:=hA) (hρ:=hρ) (hρhalf:=hρhalf) (hholder:=hholder) (j:=j) (hL:=hL)
    (h:=h) (hhH:=hhH) (haP:=haP) (hJ:=hJ) (hAs:=hAs)
    hh hspan hsmall hActual hspanF hspanC hspanS hlocalJ
    (StandardItoStoppedParameterFubini.ambient J hStopped hnull) Bg B4 B8 hBDGg hBDG4 hBDG8
  obtain ⟨Y,M0,hY,hM0,hYa,hMa,hMe⟩:=MovingOriginalGammaSharp.exists_sharp_output
    (𝓕:=𝓕) (μ:=μ) (H:=H) (Λ:=Λ) (κ:=κ) (hκ:=hκ) (haU:=haU) (haV:=haV)
    (hell:=hell) (hbU:=hbU) (hbV:=hbV) (I₀:=I₀) (I₁:=I₁) (u₀:=u₀) (S:=S)
    (J:=J) (hIJ₀:=hIJ₀) (hIJ₁:=hIJ₁) (hΛ:=zero_le_one.trans hL) (hH:=hH) (P:=P) (hκP:=hκP)
    (h:=h) (W:=Width) (hh:=by exact_mod_cast hh) (hhP:=hspan) (hW0:=wNonneg) (hcover:=by ring_nf;exact le_rfl)
    (B:=Bg) (hBDG:=hBDGg) (hsmall:=hsmallL2) (Bpast:=Bpast) (hBDGpast:=hBDGpast)
    (hL:=hL) (ha:=ha) (hA:=hA) (hρ:=hρ) (hρhalf:=hρhalf) (hholder:=hholder) (j:=j)
    (hnull:=hnull) (B0:=B0) (B1:=B1) (hBDG0:=hBDG0) (hBDG1:=hBDG1)
    (Bγ:=B) (hBDGγ:=hBDG) (hlocal:=hlocal) (Bnext:=Bnext) (hBDGnext:=hBDGnext) (hF:=hStopped)
  let M:ℝ≥0×Ω→CircleL2:=fun z=>M0 ((z.1:ℝ),z.2)
  have hM:Measurable M:=hM0.comp (NNReal.continuous_coe.measurable.prodMap measurable_id)
  have hMas:∀ᵐt∂timeMeasure (H-h),(fun ω=>M (t,ω))=ᵐ[μ] (fun ω=>Completed hh t ω):=by
    have hp:∀ᵐr:ℝ∂volume.restrict (Set.Ioc (0:ℝ) ((H-h:ℝ≥0):ℝ)),
        (fun ω=>M0 (r,ω))=ᵐ[μ] (fun ω=>Completed hh r.toNNReal ω):=by
      rw [NNReal.coe_sub hhH]
      filter_upwards [hMa,ae_restrict_mem measurableSet_Ioc] with r hr ht
      simpa only [completed,Real.coe_toNNReal _ ht.1.le] using hr
    simpa only [Real.toNNReal_coe,M] using (timeMeasurePreserving (H-h)).quasiMeasurePreserving.ae hp
  have hMass:(∫⁻z,ENNReal.ofReal (‖M z‖^2) ∂energyMeasure μ (H-h))=
      ∫⁻z,ENNReal.ofReal (‖M0 z‖^2) ∂(volume.restrict (Set.Ioc (0:ℝ) Width)).prod μ:=by
    change (∫⁻z,ENNReal.ofReal (‖M z‖^2) ∂(timeMeasure (H-h)).prod μ)=_
    rw [lintegral_prod _ ((hM.norm.pow_const 2).ennreal_ofReal.aemeasurable),timeMeasure_lintegral,
      lintegral_prod _ ((hM0.norm.pow_const 2).ennreal_ofReal.aemeasurable),NNReal.coe_sub hhH]
    apply lintegral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    simp only [M,Real.coe_toNNReal _ hr.1.le]
  let G:=NativeOutputTimePatch.field h I M
  have hG:=NativeOutputTimePatch.measurable h I M hI hM
  refine ⟨G,hG,NativeOutputTimePatch.congr_sections μ H h hhH I M _ _ hIa hMas,?_⟩
  have he:=NativeOutputTimePatch.mass μ H h hhH I M hI hM
  have hIi:(∫⁻z,ENNReal.ofReal (‖I z‖^2) ∂energyMeasure μ h)=
      ∫⁻t,∫⁻ω,ENNReal.ofReal (‖I (t,ω)‖^2) ∂μ ∂timeMeasure h:=
    lintegral_prod _ ((hI.norm.pow_const 2).ennreal_ofReal.aemeasurable)
  rw [he,hIi,hMass]
  simp only [JointGammaConstants.nativeConstant] at hIe ⊢
  exact (add_le_add hIe hMe).trans_eq (two_mul _).symm
end SHE.FullJointGammaOutput
