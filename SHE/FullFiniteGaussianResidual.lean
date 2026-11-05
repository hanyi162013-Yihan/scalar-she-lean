module
public import SHE.ActualFiniteGaussianResidual
public import SHE.ActualTerminalBandField
public import SHE.FullJointGammaClockIdentity
public import SHE.FrozenReferenceFullIdentity
public import SHE.FullOrdinaryClockIdentity
public import SHE.FullLeafClockIdentity
public import SHE.FullFirstDefectBandSections
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

namespace SHE.FullFiniteGaussianResidual
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
open scoped BigOperators
local notation "Terminal"=>ActualTerminalBandField.value
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S (a:=a) j hL hρ
local notation "Error" N:max=>FullOrdinaryHeatBandError.value
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P ha haP h j (N+1) hL ρ hρ.le
local notation "Leaf" N:max=>FullLeafClockIdentity.value
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P ha haP h j (N+1) hL ρ hρ.le
local notation "FrozenSource"=>FrozenReferenceFullIdentity.original
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P hκP (h:ℝ) hH (a:=a) j hL ρ hρ
local notation "GammaSource" hh:max=>FullJointGammaOutput.original
  (𝓕:=𝓕) (μ:=μ) (H:=H) (Λ:=Λ) (κ:=κ) (hκ:=hκ) (haU:=haU) (haV:=haV) (hell:=hell) (hbU:=hbU) (hbV:=hbV)
  (I₀:=I₀) (I₁:=I₁) (u₀:=u₀) (S:=S) (P:=P) (hκP:=hκP) (hH:=hH) (hnull:=hnull)
  (B0:=B0) (B1:=B1) (hBDG0:=hBDG0) (hBDG1:=hBDG1) (ha:=ha) (hA:=hA) (hρ:=hρ) (hρhalf:=hρhalf)
  (hholder:=hholder) (j:=j) (hL:=hL) (h:=h) (hhH:=hhH) hh

def reference(k:ℕ)(z:ℝ≥0×Ω):CircleL2:=MixedNativePairedHilbertExpansion.reference
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S J hIJ₀ hIJ₁ hnull hJ P hAs
  (z.1-h) z.1 tsub_le_self (ControlledScalarReference.observations z.1)
  (fun _=>rfl) (fun _=>rfl) RootFamily RootUniform RootMeasurable hL hρ.le k z.2
local notation "RefSource"=>reference
  (𝓕:=𝓕) (μ:=μ) (H:=H) (Λ:=Λ) (κ:=κ) (hκ:=hκ) (haU:=haU) (haV:=haV) (hell:=hell) (hbU:=hbU) (hbV:=hbV)
  (I₀:=I₀) (I₁:=I₁) (u₀:=u₀) (S:=S) (J:=J) (P:=P) (hIJ₀:=hIJ₀) (hIJ₁:=hIJ₁)
  (hnull:=hnull) (hJ:=hJ) (hAs:=hAs) (ha:=ha) (j:=j) (hL:=hL) (hρ:=hρ) (h:=h)

def higher(k:ℕ)(z:ℝ≥0×Ω):CircleL2:=MixedNativeHigherOriginalEnergy.value
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S J hIJ₀ hIJ₁ hnull hJ P hAs
  (z.1-h) z.1 tsub_le_self (ControlledScalarReference.observations z.1)
  (fun _=>rfl) (fun _=>rfl) RootFamily RootUniform RootMeasurable hL hρ.le k z.2
local notation "NoiseSource"=>higher
  (𝓕:=𝓕) (μ:=μ) (H:=H) (Λ:=Λ) (κ:=κ) (hκ:=hκ) (haU:=haU) (haV:=haV) (hell:=hell) (hbU:=hbU) (hbV:=hbV)
  (I₀:=I₀) (I₁:=I₁) (u₀:=u₀) (S:=S) (J:=J) (P:=P) (hIJ₀:=hIJ₀) (hIJ₁:=hIJ₁)
  (hnull:=hnull) (hJ:=hJ) (hAs:=hAs) (ha:=ha) (j:=j) (hL:=hL) (hρ:=hρ) (h:=h)

/-- One actual marked output is obtained from the finite comparison.
The ordinary approximation error is retained as its TOTAL sum. -/
def residual(N:ℕ)(Fr Gm:ℝ≥0×Ω→CircleL2)(Rf Nf:ℕ→ℝ≥0×Ω→CircleL2)(z:ℝ≥0×Ω):CircleL2:=
  Terminal z-Fr z+Gm z-(∑k∈Finset.range N,Rf k z)-(∑k∈Finset.range N,Nf k z)+(Error N) z-(Leaf N) z
local notation "Residual"=>residual
  (𝓕:=𝓕) (μ:=μ) (H:=H) (Λ:=Λ) (κ:=κ) (hκ:=hκ) (haU:=haU) (haV:=haV) (hell:=hell) (hbU:=hbU) (hbV:=hbV)
  (I₀:=I₀) (I₁:=I₁) (u₀:=u₀) (S:=S) (P:=P) (ha:=ha) (j:=j) (hL:=hL) (hρ:=hρ) (h:=h) (haP:=haP)

theorem measurable(N:ℕ)(Fr Gm:ℝ≥0×Ω→CircleL2)(Rf Nf:ℕ→ℝ≥0×Ω→CircleL2)
    (hFr:Measurable Fr)(hGm:Measurable Gm)(hRf:∀k,k<N→Measurable (Rf k))(hNf:∀k,k<N→Measurable (Nf k)):
    Measurable (Residual N Fr Gm Rf Nf):=by
  have ht:=ActualTerminalBandField.measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S ha j hL hρ
  have he:=FullOrdinaryHeatBandError.measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P ha haP h j (N+1) hL ρ hρ.le
  have hl:Measurable (Leaf N):=(MixedNativeFullLeafHilbert.field_measurable
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h RootFamily RootUniform RootMeasurable hL hρ.le (N+1)).comp
      (NNReal.continuous_coe.measurable.prodMap measurable_id)
  exact (((((ht.sub hFr).add hGm).sub (Finset.measurable_sum _ (fun k hk=>hRf k (Finset.mem_range.mp hk)))).sub
    (Finset.measurable_sum _ (fun k hk=>hNf k (Finset.mem_range.mp hk)))).add he).sub hl

include hIJ₀ hIJ₁ hBDG hJ hAs in
/-- The versions supplied by the actual component constructions give
the literal full first-defect sum on genuine time/sample sections.
No measurability of the raw equality event is used. -/
theorem identified(hh:0<h)
    (hsmall:ProfileStability.memoryConstant P.lower P.holder P.exponent*
      ProfileVolterra.powerConstant ((P.exponent-2)/4)*P.horizon^(P.exponent/4)≤1/2)
    (hActual:P.coefficient=(fun z=>κ+aV z))
    (hlocalJ:StandardTerminalPastLocality J)(hFubini:StandardItoParameterFubini J)
    (N:ℕ)(Fr Gm:ℝ≥0×Ω→CircleL2)(Rf Nf:ℕ→ℝ≥0×Ω→CircleL2)
    (hFr:∀ᵐt∂timeMeasure H,∀ᵐω∂μ,Fr (t,ω)=FrozenSource (t,ω))
    (hGm:∀ᵐt∂timeMeasure H,∀ᵐω∂μ,Gm (t,ω)=(GammaSource hh) (t,ω))
    (hRf:∀ᵐt∂timeMeasure H,∀ᵐω∂μ,∀k,k<N→Rf k (t,ω)=RefSource (k+1) (t,ω))
    (hNf:∀ᵐt∂timeMeasure H,∀ᵐω∂μ,∀k,k<N→Nf k (t,ω)=NoiseSource (k+1) (t,ω)):
    ∀ᵐt∂timeMeasure H,∀ᵐω∂μ,Residual N Fr Gm Rf Nf (t,ω)=
      ∑k∈Finset.range (N+1),FullFirstDefectBandEnergy.term
        𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P hAs ha h j hL hρ.le k (t,ω):=by
  have he:=FullOrdinaryClockIdentity.identity_ae
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P hAs ha haP J hIJ₀ hIJ₁ hnull hJ hsmall
    hActual h j (N+1) hL ρ hρ.le
  have hl:=FullLeafClockIdentity.identity_ae
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P hAs ha haP J hIJ₀ hIJ₁ hnull hJ hsmall
    hActual h j (N+1) hL ρ hρ.le
  filter_upwards [hFr,hGm,hRf,hNf,timeMeasure_ae_mem H] with t hfr hgm hrf hnf ht
  have hp:t-h<t:=by
    by_cases hht:h≤t
    · apply NNReal.coe_lt_coe.mp
      rw [NNReal.coe_sub hht]
      exact sub_lt_self _ (by exact_mod_cast hh)
    · rw [tsub_eq_zero_of_le (le_of_not_ge hht)]
      exact ht.1
  have hf:=ActualFiniteGaussianResidual.residual_eq_sum
    (𝓕:=𝓕) (μ:=μ) (H:=H) (Λ:=Λ) (κ:=κ) (hκ:=hκ) (haU:=haU) (haV:=haV) (hell:=hell) (hbU:=hbU) (hbV:=hbV)
    (I₀:=I₀) (I₁:=I₁) (u₀:=u₀) (S:=S) (J:=J) (P:=P) (hκP:=hκP) (hΛ:=zero_le_one.trans hL)
    (v:=t-h) (b:=t) (hbH:=ht.2) (hH:=hH) (B:=B) (hBDG:=hBDG) (hIJ₀:=hIJ₀) (hIJ₁:=hIJ₁) (hvb:=tsub_le_self)
    (ha:=ha) (j:=j) (hb0:=ht.1) (hnull:=hnull) (B0:=B0) (B1:=B1) (hBDG0:=hBDG0) (hBDG1:=hBDG1)
    (hA:=hA) (hβ:=P.exponent_pos.le) (hβ1:=P.exponent_le_one) (hh:=hholder)
    (hsmall:=hsmall) (hAs:=hAs) (hJ:=hJ) (hL:=hL) (hρ:=hρ) (hρhalf:=hρhalf)
    haP hActual hlocalJ hFubini hp N
  filter_upwards [hfr,hgm,hrf,hnf,he,hl,hf] with ω hfr hgm hrf hnf he hl hf
  have hg:=FullJointGammaClockIdentity.identity
    (𝓕:=𝓕) (μ:=μ) (H:=H) (Λ:=Λ) (κ:=κ) (hκ:=hκ) (haU:=haU) (haV:=haV) (hell:=hell) (hbU:=hbU) (hbV:=hbV)
    (I₀:=I₀) (I₁:=I₁) (u₀:=u₀) (S:=S) (P:=P) (hκP:=hκP) (hH:=hH) (hnull:=hnull)
    (B0:=B0) (B1:=B1) (hBDG0:=hBDG0) (hBDG1:=hBDG1) (ha:=ha) (hA:=hA) (hρ:=hρ) (hρhalf:=hρhalf)
    (hholder:=hholder) (j:=j) (hL:=hL) (h:=h) (hhH:=hhH) hh t ht.1 ht.2 ω
  have hfr':Fr (t,ω)=JointGammaRootHilbertPair.frozen
      𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P hκP (t-h) t ht.2 hH (a:=a) j hL hρ ω:=by
    simpa only [FrozenReferenceFullIdentity.original,min_eq_left ht.2,Real.toNNReal_coe] using hfr
  dsimp only [residual]
  rw [hfr',hgm,hg,ActualTerminalBandField.at_time,he t ht.1,hl t ht.1 ht.2]
  have hrEq:(∑k∈Finset.range N,Rf k (t,ω))=(∑k∈Finset.range N,RefSource (k+1) (t,ω)):=
    Finset.sum_congr rfl (fun k hk=>hrf k (Finset.mem_range.mp hk))
  have hnEq:(∑k∈Finset.range N,Nf k (t,ω))=(∑k∈Finset.range N,NoiseSource (k+1) (t,ω)):=
    Finset.sum_congr rfl (fun k hk=>hnf k (Finset.mem_range.mp hk))
  rw [hrEq,hnEq]
  exact hf

/-- Seven exact full-time pieces, retaining the norm of the TOTAL
ordinary error. Quantitative bounds are attached to these actual slots. -/
theorem seven_piece(N:ℕ)(Fr Gm:ℝ≥0×Ω→CircleL2)(Rf Nf:ℕ→ℝ≥0×Ω→CircleL2):
    eLpNorm Terminal 2 (energyMeasure μ H)≤eLpNorm Fr 2 (energyMeasure μ H)+eLpNorm Gm 2 (energyMeasure μ H)+
      (∑k∈Finset.range N,eLpNorm (Rf k) 2 (energyMeasure μ H))+
      (∑k∈Finset.range N,eLpNorm (Nf k) 2 (energyMeasure μ H))+
      eLpNorm (Residual N Fr Gm Rf Nf) 2 (energyMeasure μ H)+
      eLpNorm (Error N) 2 (energyMeasure μ H)+eLpNorm (Leaf N) 2 (energyMeasure μ H):=by
  let T:Fin 7→(ℝ≥0×Ω)→CircleL2:=![Fr,-Gm,∑k∈Finset.range N,Rf k,∑k∈Finset.range N,Nf k,
    Residual N Fr Gm Rf Nf,-(Error N),(Leaf N)]
  have he:Terminal=∑i:Fin 7,T i:=by
    funext z
    simp only [T,Fin.sum_univ_succ,Matrix.cons_val_zero,Matrix.cons_val_succ,Fin.sum_univ_zero,
      Finset.sum_empty,add_zero,Finset.sum_apply,Pi.neg_apply,residual]
    abel
  calc
    _=eLpNorm (∑i:Fin 7,T i) 2 (energyMeasure μ H):=congrArg (fun f=>eLpNorm f 2 (energyMeasure μ H)) he
    _≤∑i:Fin 7,eLpNorm (T i) 2 (energyMeasure μ H):=eLpNorm_sum_le (by norm_num)
    _≤_:=by
      simp only [T,Fin.sum_univ_succ,Matrix.cons_val_zero,Matrix.cons_val_succ,Fin.sum_univ_zero,
        Finset.sum_empty,add_zero,eLpNorm_neg,add_assoc]
      gcongr
      all_goals exact eLpNorm_sum_le (μ:=energyMeasure μ H) (p:=2) (by norm_num)

include hIJ₀ hIJ₁ hBDG hJ hAs in
/-- Actual full-time marked residual energy, with the sharp finite-depth
coefficient and original negative-input energy. No mark bound is assumed. -/
theorem marked_energy(hh:0<h)
    (hsmall:ProfileStability.memoryConstant P.lower P.holder P.exponent*
      ProfileVolterra.powerConstant ((P.exponent-2)/4)*P.horizon^(P.exponent/4)≤1/2)
    (hActual:P.coefficient=(fun z=>κ+aV z))
    (hlocalJ:StandardTerminalPastLocality J)(hFubini:StandardItoParameterFubini J)
    (N:ℕ)(Fr Gm:ℝ≥0×Ω→CircleL2)(Rf Nf:ℕ→ℝ≥0×Ω→CircleL2)
    (hFr:∀ᵐt∂timeMeasure H,∀ᵐω∂μ,Fr (t,ω)=FrozenSource (t,ω))
    (hGm:∀ᵐt∂timeMeasure H,∀ᵐω∂μ,Gm (t,ω)=(GammaSource hh) (t,ω))
    (hRf:∀ᵐt∂timeMeasure H,∀ᵐω∂μ,∀k,k<N→Rf k (t,ω)=RefSource (k+1) (t,ω))
    (hNf:∀ᵐt∂timeMeasure H,∀ᵐω∂μ,∀k,k<N→Nf k (t,ω)=NoiseSource (k+1) (t,ω))
    (hmFr:Measurable Fr)(hmGm:Measurable Gm)(hmRf:∀k,k<N→Measurable (Rf k))(hmNf:∀k,k<N→Measurable (Nf k))
    (hM:0≤M)(hspan:(h:ℝ)≤P.horizon)
    (hAge:∀k,k≤N→(h:ℝ)≤ControlledDefectConstants.horizon P.lower P.lower_pos ell M hell hM ρ hρ hρhalf k)
    (hOld:∀r,r<N→(h:ℝ)≤PhysicalScoreChain.uniformHorizon 1 r)
    (Broot:ℝ)(hBroot:∀z,|a z|≤Broot)(η:ℝ)(hη:0<η)
:
    Integrable (fun z=>‖Residual N Fr Gm Rf Nf z‖^2) (energyMeasure μ H) ∧
      (∫z,‖Residual N Fr Gm Rf Nf z‖^2 ∂energyMeasure μ H)≤
        DefectGapFiniteCoefficient.constant P (ControlledOldIntervals.fraction P*P.lower) (PhysicalScoreChain.uniformConstant 1)
          (ScalarHeatBandBernstein.amplitude Broot A P.exponent N) η N
            (fun i=>ControlledDefectConstants.constant ell M hell hM ρ hρ hρhalf i P)*
          DefectGapFiniteCoefficient.clock Λ ρ^2*((2:ℝ)^(j+1))^(-2*(P.exponent-η))*(Neg).toReal:=by
  have hid:=identified
    (𝓕:=𝓕) (μ:=μ) (H:=H) (Λ:=Λ) (κ:=κ) (hκ:=hκ) (haU:=haU) (haV:=haV) (hell:=hell) (hbU:=hbU) (hbV:=hbV)
    (I₀:=I₀) (I₁:=I₁) (u₀:=u₀) (S:=S) (J:=J) (P:=P) (hκP:=hκP) (hH:=hH)
    (B:=B) (hBDG:=hBDG) (hIJ₀:=hIJ₀) (hIJ₁:=hIJ₁) (ha:=ha) (j:=j) (hnull:=hnull)
    (B0:=B0) (B1:=B1) (hBDG0:=hBDG0) (hBDG1:=hBDG1) (hA:=hA) (hholder:=hholder)
    (hAs:=hAs) (hJ:=hJ) (hL:=hL) (hρ:=hρ) (hρhalf:=hρhalf) (h:=h) (hhH:=hhH) (haP:=haP)
    hh hsmall hActual hlocalJ hFubini N Fr Gm Rf Nf hFr hGm hRf hNf
  have hResidualMeas:=measurable
    (𝓕:=𝓕) (μ:=μ) (H:=H) (Λ:=Λ) (κ:=κ) (hκ:=hκ) (haU:=haU) (haV:=haV) (hell:=hell) (hbU:=hbU) (hbV:=hbV)
    (I₀:=I₀) (I₁:=I₁) (u₀:=u₀) (S:=S) (P:=P) (ha:=ha) (j:=j) (hL:=hL) (hρ:=hρ) (h:=h) (haP:=haP)
    N Fr Gm Rf Nf hmFr hmGm hmRf hmNf
  exact FullFirstDefectBandSections.energy_sections
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P hAs ha hsmall hM hActual
    ρ hL hρ hρhalf N h hh ((show (h:ℝ)≤(H:ℝ) by exact_mod_cast hhH).trans hH)
    hspan hAge hOld hBroot hA P.exponent_pos.le P.exponent_le_one hholder j η hη
    (Residual N Fr Gm Rf Nf) hResidualMeas hid
end SHE.FullFiniteGaussianResidual
