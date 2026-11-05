module
public import SHE.FullJointGammaOutput

@[expose] public section
noncomputable section

set_option autoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 2300000

namespace SHE.FullJointGammaClockIdentity
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

/-- The literal native first-pair Gamma at the physical terminal and
its truncated moving past. -/
def actual(t:ℝ≥0)(htH:t≤H)(ht:0<t)(ω:Ω):CircleL2:=
  NativeHeatObservation.embed (MixedNativeJointGammaOutput.value
    (𝓕:=𝓕) (μ:=μ) (H:=H) (Λ:=Λ) (κ:=κ) (hκ:=hκ) (haU:=haU) (haV:=haV)
    (hell:=hell) (hbU:=hbU) (hbV:=hbV) (I₀:=I₀) (I₁:=I₁) (u₀:=u₀) (v₀:=u₀) (S:=S)
    (P:=P) (hκP:=hκP) (v:=t-h) (b:=t) (hbH:=htH)
    (hb1:=(show (t:ℝ)≤(H:ℝ) by exact_mod_cast htH).trans hH)
    (hb0:=ht) (hnull:=hnull) (B0:=B0) (B1:=B1) (hBDG0:=hBDG0) (hBDG1:=hBDG1)
    (ha:=ha) (hA:=hA) (hβ:=P.exponent_pos.le) (hβ1:=P.exponent_le_one)
    (hh:=hholder) (j:=j) (hΛ:=hL) (hρ:=hρ) (hρhalf:=hρhalf) ω)
local notation "Actual"=>actual
  (𝓕:=𝓕) (μ:=μ) (H:=H) (Λ:=Λ) (κ:=κ) (hκ:=hκ) (haU:=haU) (haV:=haV) (hell:=hell) (hbU:=hbU) (hbV:=hbV)
  (I₀:=I₀) (I₁:=I₁) (u₀:=u₀) (S:=S) (P:=P) (hκP:=hκP) (hH:=hH) (hnull:=hnull)
  (B0:=B0) (B1:=B1) (hBDG0:=hBDG0) (hBDG1:=hBDG1) (ha:=ha) (hA:=hA) (hρ:=hρ) (hρhalf:=hρhalf)
  (hholder:=hholder) (j:=j) (hL:=hL) (h:=h)
local notation "Original"=>FullJointGammaOutput.original
  (𝓕:=𝓕) (μ:=μ) (H:=H) (Λ:=Λ) (κ:=κ) (hκ:=hκ) (haU:=haU) (haV:=haV) (hell:=hell) (hbU:=hbU) (hbV:=hbV)
  (I₀:=I₀) (I₁:=I₁) (u₀:=u₀) (S:=S) (P:=P) (hκP:=hκP) (hH:=hH) (hnull:=hnull)
  (B0:=B0) (B1:=B1) (hBDG0:=hBDG0) (hBDG1:=hBDG1) (ha:=ha) (hA:=hA) (hρ:=hρ) (hρhalf:=hρhalf)
  (hholder:=hholder) (j:=j) (hL:=hL) (h:=h) (hhH:=hhH)

/-- Both branches of the full measurable Gamma construction are the
literal Gamma appearing in the finite Gaussian comparison. -/
theorem identity(hh:0<h)(t:ℝ≥0)(ht:0<t)(htH:t≤H)(ω:Ω):
    Original hh (t,ω)=Actual t htH ht ω:=by
  by_cases hth:t≤h
  · have htr:0<(t:ℝ)∧(t:ℝ)≤(h:ℝ):=⟨by exact_mod_cast ht,by exact_mod_cast hth⟩
    simp only [FullJointGammaOutput.original,NativeOutputTimePatch.field,if_pos hth,
      InitialJointGammaEnergy.output,dif_pos htr,actual,Real.toNNReal_coe,tsub_eq_zero_of_le hth]
  · have hlt:h<t:=lt_of_not_ge hth
    have hle:h≤t:=hlt.le
    have hr:((t-h:ℝ≥0):ℝ)∈Set.Ioc (0:ℝ) Width:=by
      rw [NNReal.coe_sub hle]
      refine ⟨?_,?_⟩
      · exact sub_pos.mpr (by exact_mod_cast hlt)
      · exact sub_le_sub_right (by exact_mod_cast htH) _
    have hv:NativeMovingGammaClock.past Width ((t-h:ℝ≥0):ℝ)=t-h:=by
      rw [NativeMovingGammaClock.past_eq hr,Real.toNNReal_coe]
    have hb:NativeMovingGammaClock.terminal Width (h:ℝ) ((t-h:ℝ≥0):ℝ)=t:=by
      rw [NativeMovingGammaClock.terminal_eq hr]
      simp only [←NNReal.coe_add,Real.toNNReal_coe,tsub_add_cancel_of_le hle]
    simp only [FullJointGammaOutput.original,NativeOutputTimePatch.field,if_neg hth,
      FullJointGammaOutput.completed,MovingOriginalGammaHilbert.output,hv,hb,actual]

end SHE.FullJointGammaClockIdentity
