module

public import SHE.MixedNativeJointRowBudgets
public import SHE.MixedNativeMovingJointBudgets
public import SHE.MixedNativeJointSlotEnvelopes
public import SHE.MixedNativeJointGammaOutput
public import SHE.MixedNativeJointGammaPhysicalBudget
public import SHE.MixedNativeSignedBudget
public import SHE.MixedNativeJointDirectBudget
public import SHE.MixedNativeMovingFrozenFactor
public import SHE.MixedNativePastBudget
public import SHE.GammaBandConstants
public import SHE.NativeMovingGammaClock
public import SHE.MixedMovingEnergy

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 2200000
namespace SHE.MixedNativeJointGammaEnvelope
open Set MeasureTheory PredictableL2 NativeHeatObservation NativeObservationNaturality
  FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation
open scoped NNReal ENNReal
local instance mixedNativeMovingCurrentGamma_realSigma : MeasurableSpace RealL2:=borel _
local instance mixedNativeMovingCurrentGamma_realBorel : BorelSpace RealL2:=⟨rfl⟩
local instance mixedNativeMovingCurrentGamma_unitSigma : MeasurableSpace CircleHeat.CircleL2:=borel _
local instance mixedNativeMovingCurrentGamma_unitBorel : BorelSpace CircleHeat.CircleL2:=⟨rfl⟩
local instance mixedNativeMovingCurrentGamma_period : Fact (0<2*Real.pi):=⟨by positivity⟩
local instance mixedNativeMovingCurrentGamma_rowSigma : MeasurableSpace RealHaarInput:=borel _
local instance mixedNativeMovingCurrentGamma_rowBorel : BorelSpace RealHaarInput:=⟨rfl⟩
local instance mixedNativeMovingCurrentGamma_blockSigma : MeasurableSpace (Both RealHaarInput):=borel _
local instance mixedNativeMovingCurrentGamma_blockBorel : BorelSpace (Both RealHaarInput):=⟨rfl⟩
local instance mixedNativeMovingCurrentGamma_columnsSigma : MeasurableSpace RealHaarIntegrand.Columns:=borel _
local instance mixedNativeMovingCurrentGamma_columnsBorel : BorelSpace RealHaarIntegrand.Columns:=⟨rfl⟩
local instance mixedNativeMovingCurrentGamma_unitPos : Fact (0<(1:ℝ)):=⟨zero_lt_one⟩
local instance mixedNativeMovingCurrentGamma_unitSecond : SecondCountableTopology CircleHeat.CircleL2:=
  (_root_.fourierBasis (T:=(1:ℝ))).repr.toHomeomorph.secondCountableTopology
local instance mixedNativeMovingCurrentGamma_realSecond : SecondCountableTopology RealL2:=
  FiniteHaar.realCircleIdentification.toHomeomorph.secondCountableTopology
variable {Ω : Type} [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
variable (Λ κ : ℝ) (hκ : 0<κ) {aU aV : ℝ→ℝ} (haU : Measurable aU) (haV : Measurable aV) {ell M : ℝ}
variable (hell : 0<ell) (hbU : ∀ z,ell≤aU z ∧ aU z≤M) (hbV : ∀ z,ell≤aV z ∧ aV z≤M)
variable (I₀ I₁ : StandardTerminalIto (C:=RealHaarIntegrand.Columns) (E:=RealL2) 𝓕 μ H)
variable (u₀ : RealL2)
variable (S : MixedNativeAdditiveResidualPair.Solution 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀)



variable (J : StandardTerminalIto (C:=Both RealHaarInput) (E:=ℝ) 𝓕 μ H)
variable (hIJ₀ : StandardScalarNaturality I₀ (leftIntegral 𝓕 μ H J))
variable (hIJ₁ : StandardScalarNaturality I₁ (rightIntegral 𝓕 μ H J))
variable (hΛ : 0≤Λ) (hH : (H:ℝ)≤1) (B : ℝ≥0) (hBDG : StandardTerminalBDGPower 1 J B)
variable (P:CanonicalCovariance.ProfileParameters) (hκP:κ<P.lower)
variable (h W:ℝ) (hh:0<h) (hhP:h≤P.horizon) (hW0:0≤W) (hcover:W+h≤H)
variable (hsmall:ProfileStability.memoryConstant P.lower P.holder P.exponent*
  ProfileVolterra.powerConstant ((P.exponent-1)/4)*P.horizon^(P.exponent/4)≤1/2)
variable (Bpast:ℝ≥0) (hBDGpast:StandardTerminalBDGPower 2 J Bpast)

local notation "Past"=>NativeMovingGammaClock.past W
local notation "Terminal"=>NativeMovingGammaClock.terminal W h
local notation "covered" r=>NativeMovingGammaClock.terminal_le hW0 hh.le H hcover r
local notation "ordered" r=>NativeMovingGammaClock.past_lt hW0 hh r
local notation "span" r=>NativeMovingGammaClock.span hW0 hh.le r
local notation "Global"=>MixedMovingEnergy.globalEnergy 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S

local notation "Budget"=>MixedNativeMovingJointBudgets.budget 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S hH P hκP h W hh hW0 hcover
local notation "Factor"=>MixedNativeMovingFrozenFactor.budget 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P hκP h W
local notation "E" r=>MixedMovingEnergy.energy 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S (r:ℝ).toNNReal

variable (hL:1≤Λ) {a:ℝ→ℝ} (ha:SmoothCylinders.BoundedSmooth a) {A ρ:ℝ} (hA:0≤A)
variable (hρ:0<ρ) (hρhalf:ρ<1/2) (hholder:∀x y,|a x-a y|≤A*|x-y|^P.exponent) (j:ℕ)
variable (hnull:NullCompleteFiltration.ContainsNullSets 𝓕 μ)
variable (B0 B1:ℝ≥0) (hBDG0:StandardTerminalBDG16 I₀ B0) (hBDG1:StandardTerminalBDG16 I₁ B1)
local notation "Lower"=>MixedNativeGammaEnergy.commonLower (ell:=ell) (P:=P) (κ:=κ)
local notation "Upper"=>MixedNativeGammaEnergy.commonUpper (M:=M) (P:=P) (κ:=κ)
local notation "LowerPos"=>MixedNativeGammaEnergy.commonLower_pos (ell:=ell) (P:=P) (κ:=κ) (hell:=hell) (hκP:=hκP)
local notation "Trace"=>NativeConvexGammaUniform.constant Lower Upper LowerPos hρ hρhalf
local notation "Higher"=>HaarWeightedHeat.higherConstant Lower Upper LowerPos 0 ρ
local notation "Ksum"=>(κ+Upper)*(1+2*HeatTrace.fractionalGaussianIntegral ρ)
local notation "Signed"=>MixedNativeSignedBudget.value 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P hL hρ.le A j h
local notation "Direct"=>MixedNativeJointDirectBudget.direct 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P h a j ρ
local notation "Variance"=>MixedNativeJointSlotEnvelopes.variance 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P h A ρ j
local notation "FactorEnvelope"=>MixedNativeJointSlotEnvelopes.factor 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P h A ρ j
local notation "Root"=>MixedNativeJointSlotEnvelopes.root 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P A ρ j

def signedMass (r:ℝ):ℝ≥0∞:=∫⁻τ in Ioc (0:ℝ) ((Terminal r:ℝ)-(Past r:ℝ)),
  MixedNativeSignedGammaRows.sectionEnergy 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P hL hρ.le A j (Past r) (Terminal r) τ
local notation "SignedMass"=>signedMass (𝓕:=𝓕) (μ:=μ) (H:=H) (Λ:=Λ) (κ:=κ) (hκ:=hκ)
    (haU:=haU) (haV:=haV) (hell:=hell) (hbU:=hbU) (hbV:=hbV) (I₀:=I₀)
    (I₁:=I₁) (u₀:=u₀) (S:=S) (P:=P) (h:=h) (W:=W)
    (hL:=hL) (hρ:=hρ) (A:=A) (j:=j)

/-- A single genuinely Borel six-slot envelope, formed after replacing
parameterwise frozen versions by measurable ORIGINAL past-energy caps. -/
def value (Bnext:ℝ≥0)(r:ℝ):ℝ≥0∞:=6*(ENNReal.ofReal Trace*Signed r+
  ENNReal.ofReal Higher*FactorEnvelope r+ENNReal.ofReal Ksum*(Direct r+Variance r+Root Bnext r+Variance r))

/-- Constructed ORIGINAL physical Hilbert Gamma energy on every legal
clamped moving window. No measurable joint reference version is asserted. -/
def energy (r:ℝ):ℝ≥0∞:=MixedNativeJointGammaOutput.energy
    (𝓕:=𝓕) (μ:=μ) (H:=H) (Λ:=Λ) (κ:=κ) (hκ:=hκ)
    (haU:=haU) (haV:=haV) (hell:=hell) (hbU:=hbU) (hbV:=hbV) (I₀:=I₀)
    (I₁:=I₁) (u₀:=u₀) (S:=S) (P:=P) (hκP:=hκP) (hnull:=hnull)
    (B0:=B0) (B1:=B1) (hBDG0:=hBDG0) (hBDG1:=hBDG1) (ha:=ha) (hA:=hA)
    (j:=j) (ρ:=ρ) (hρ:=hρ) (hρhalf:=hρhalf) (v₀:=u₀) (v:=Past r)
    (b:=Terminal r) (hbH:=covered r) (hb1:=((show (Terminal r:ℝ)≤(H:ℝ) by exact_mod_cast covered r).trans hH)) (hb0:=NativeMovingGammaClock.terminal_pos hW0 hh r) (hΛ:=hL) (hβ:=P.exponent_pos.le)
    (hβ1:=P.exponent_le_one) (hh:=hholder)

local notation "Energy"=>energy (𝓕:=𝓕) (μ:=μ) (H:=H) (Λ:=Λ) (κ:=κ) (hκ:=hκ)
    (haU:=haU) (haV:=haV) (hell:=hell) (hbU:=hbU) (hbV:=hbV) (I₀:=I₀)
    (I₁:=I₁) (u₀:=u₀) (S:=S) (P:=P) (hκP:=hκP) (hH:=hH)
    (hh:=hh) (hW0:=hW0) (hcover:=hcover) (h:=h) (W:=W) (hL:=hL)
    (ha:=ha) (hA:=hA) (hρ:=hρ) (hρhalf:=hρhalf) (hholder:=hholder) (j:=j)
    (hnull:=hnull) (B0:=B0) (B1:=B1) (hBDG0:=hBDG0) (hBDG1:=hBDG1)
local notation "Value"=>value (𝓕:=𝓕) (μ:=μ) (H:=H) (Λ:=Λ) (κ:=κ) (hκ:=hκ)
    (haU:=haU) (haV:=haV) (hell:=hell) (hbU:=hbU) (hbV:=hbV) (I₀:=I₀)
    (I₁:=I₁) (u₀:=u₀) (S:=S) (P:=P) (hκP:=hκP) (h:=h)
    (hL:=hL) (A:=A) (ρ:=ρ) (hρ:=hρ) (hρhalf:=hρhalf) (j:=j)
    (a:=a)

include ha in
/-- The complete dominating envelope is genuinely Borel in the moving
past, independently of all parameterwise frozen stochastic versions. -/
theorem value_measurable (Bnext:ℝ≥0):Measurable (Value Bnext):=by
  have hs:=MixedNativeSignedBudget.measurable
      (𝓕:=𝓕) (μ:=μ) (H:=H) (Λ:=Λ) (κ:=κ) (hκ:=hκ)
      (haU:=haU) (haV:=haV) (hell:=hell) (hbU:=hbU) (hbV:=hbV) (I₀:=I₀)
      (I₁:=I₁) (u₀:=u₀) (S:=S) (P:=P) (j:=j) (ρ:=ρ)
      (A:=A) (h:=h) (hL:=hL) (hρ:=hρ.le)
  have hc:=MixedNativeJointDirectBudget.direct_measurable
      (𝓕:=𝓕) (μ:=μ) (H:=H) (Λ:=Λ) (κ:=κ) (hκ:=hκ)
      (haU:=haU) (haV:=haV) (hell:=hell) (hbU:=hbU) (hbV:=hbV) (I₀:=I₀)
      (I₁:=I₁) (u₀:=u₀) (S:=S) (P:=P) (h:=h) (ha:=ha)
      (j:=j) (ρ:=ρ)
  have hv:=MixedNativeJointSlotEnvelopes.variance_measurable
      (𝓕:=𝓕) (μ:=μ) (H:=H) (Λ:=Λ) (κ:=κ) (hκ:=hκ)
      (haU:=haU) (haV:=haV) (hell:=hell) (hbU:=hbU) (hbV:=hbV) (I₀:=I₀)
      (I₁:=I₁) (u₀:=u₀) (S:=S) (P:=P) (h:=h) (A:=A)
      (ρ:=ρ) (j:=j)
  have hf:=MixedNativeJointSlotEnvelopes.factor_measurable
      (𝓕:=𝓕) (μ:=μ) (H:=H) (Λ:=Λ) (κ:=κ) (hκ:=hκ)
      (haU:=haU) (haV:=haV) (hell:=hell) (hbU:=hbU) (hbV:=hbV) (I₀:=I₀)
      (I₁:=I₁) (u₀:=u₀) (S:=S) (P:=P) (h:=h) (A:=A)
      (ρ:=ρ) (j:=j)
  have hr:=MixedNativeJointSlotEnvelopes.root_measurable
      (𝓕:=𝓕) (μ:=μ) (H:=H) (Λ:=Λ) (κ:=κ) (hκ:=hκ)
      (haU:=haU) (haV:=haV) (hell:=hell) (hbU:=hbU) (hbV:=hbV) (I₀:=I₀)
      (I₁:=I₁) (u₀:=u₀) (S:=S) (P:=P) (A:=A) (ρ:=ρ)
      (j:=j) (Bnext:=Bnext)
  exact (((hs.const_mul _).add (hf.const_mul _)).add
    ((((hc.add hv).add hr).add hv).const_mul _)).const_mul 6

variable (Bγ:ℝ≥0) (hBDGγ:StandardTerminalBDG16 J Bγ)
variable (hlocal:StandardTerminalPastLocality I₁) (Bnext:ℝ≥0) (hBDGnext:StandardTerminalBDGPower 1 I₁ Bnext)
include hIJ₀ hIJ₁ hΛ hsmall hBDGpast hhP hBDGγ hlocal hBDGnext in
/-- All SIX actual original physical Gamma terms are bounded at EACH
covered past by one genuinely Borel envelope. Frozen versions are
replaced pointwise before summing or taking the outer past integral. -/
theorem energy_le (r:ℝ)(hr:r∈Ioc (0:ℝ) W):Energy r≤Value Bnext r:=by
  have he:Energy r≤6*(ENNReal.ofReal Trace*SignedMass r+ENNReal.ofReal Higher*Factor A ρ j r+
      ENNReal.ofReal Ksum*(Budget a j ρ 0 1 r+Budget a j ρ 1 2 r+Budget a j ρ 3 4 r+Budget a j ρ 4 5 r)):=by
    exact MixedNativeJointGammaPhysicalBudget.actual_complete_energy
      (𝓕:=𝓕) (μ:=μ) (H:=H) (Λ:=Λ) (κ:=κ) (hκ:=hκ)
      (haU:=haU) (haV:=haV) (hell:=hell) (hbU:=hbU) (hbV:=hbV) (I₀:=I₀)
      (I₁:=I₁) (u₀:=u₀) (S:=S) (P:=P) (hκP:=hκP) (J:=J)
      (hIJ₀:=hIJ₀) (hIJ₁:=hIJ₁) (ha:=ha) (hA:=hA) (hholder:=hholder) (hH:=hH)
      (j:=j) (ρ:=ρ) (hρ:=hρ) (hρhalf:=hρhalf) (hnull:=hnull) (B0:=B0)
      (B1:=B1) (hBDG0:=hBDG0) (hBDG1:=hBDG1) (v:=Past r) (b:=Terminal r) (hbH:=covered r)
      (hb1:=((show (Terminal r:ℝ)≤(H:ℝ) by exact_mod_cast covered r).trans hH)) (hb0:=NativeMovingGammaClock.terminal_pos hW0 hh r) (hΛ:=hL)
  have hs:SignedMass r≤Signed r:=by
    dsimp only [signedMass]
    rw [span r,NativeMovingGammaClock.past_eq hr,NativeMovingGammaClock.terminal_eq hr h]
    exact MixedNativeSignedBudget.native_le
      (𝓕:=𝓕) (μ:=μ) (H:=H) (Λ:=Λ) (κ:=κ) (hκ:=hκ)
      (haU:=haU) (haV:=haV) (hell:=hell) (hbU:=hbU) (hbV:=hbV) (I₀:=I₀)
      (I₁:=I₁) (u₀:=u₀) (S:=S) (P:=P) (j:=j) (ρ:=ρ)
      (A:=A) (h:=h) (r:=r) (hL:=hL) (hρ:=hρ.le) (hr:=hr.1)
      (hh:=hh) (hcover:=(by linarith [hr.2,hcover]:r+h≤H))
  have hc:=MixedNativeJointDirectBudget.current_eq
    (𝓕:=𝓕) (μ:=μ) (H:=H) (Λ:=Λ) (κ:=κ) (hκ:=hκ)
      (haU:=haU) (haV:=haV) (hell:=hell) (hbU:=hbU) (hbV:=hbV) (I₀:=I₀)
      (I₁:=I₁) (u₀:=u₀) (S:=S) (P:=P) (hκP:=hκP) (hH:=hH)
      (h:=h) (W:=W) (hh:=hh) (hW0:=hW0) (hcover:=hcover) (ha:=ha)
      (hA:=hA) (hholder:=hholder) (j:=j) (ρ:=ρ) (r:=r) (hr:=hr)
  have hv:=MixedNativeJointSlotEnvelopes.current_variance_le
    (𝓕:=𝓕) (μ:=μ) (H:=H) (Λ:=Λ) (κ:=κ) (hκ:=hκ)
      (haU:=haU) (haV:=haV) (hell:=hell) (hbU:=hbU) (hbV:=hbV) (I₀:=I₀)
      (I₁:=I₁) (u₀:=u₀) (S:=S) (P:=P) (hκP:=hκP) (J:=J)
      (hIJ₀:=hIJ₀) (hIJ₁:=hIJ₁) (hΛ:=hΛ) (hH:=hH) (h:=h) (W:=W)
      (hh:=hh) (hhP:=hhP) (hW0:=hW0) (hcover:=hcover) (hsmall:=hsmall) (Bpast:=Bpast)
      (hBDGpast:=hBDGpast) (ha:=ha) (hA:=hA) (hholder:=hholder) (hnull:=hnull) (B0:=B0)
      (B1:=B1) (hBDG0:=hBDG0) (hBDG1:=hBDG1) (j:=j) (r:=r) (hr:=hr)
      (hρ0:=(by linarith : -(1/2:ℝ)<ρ)) (hρ1:=hρhalf)
  have hv1:=MixedNativeJointSlotEnvelopes.reference_variance_le
    (𝓕:=𝓕) (μ:=μ) (H:=H) (Λ:=Λ) (κ:=κ) (hκ:=hκ)
      (haU:=haU) (haV:=haV) (hell:=hell) (hbU:=hbU) (hbV:=hbV) (I₀:=I₀)
      (I₁:=I₁) (u₀:=u₀) (S:=S) (P:=P) (hκP:=hκP) (J:=J)
      (hIJ₀:=hIJ₀) (hIJ₁:=hIJ₁) (hΛ:=hΛ) (hH:=hH) (h:=h) (W:=W)
      (hh:=hh) (hhP:=hhP) (hW0:=hW0) (hcover:=hcover) (hsmall:=hsmall) (Bpast:=Bpast)
      (hBDGpast:=hBDGpast) (ha:=ha) (hA:=hA) (hholder:=hholder) (hnull:=hnull) (B0:=B0)
      (B1:=B1) (hBDG0:=hBDG0) (hBDG1:=hBDG1) (j:=j) (r:=r) (hr:=hr)
      (hρ0:=(by linarith : -(1/2:ℝ)<ρ)) (hρ1:=hρhalf)
  have hf:=MixedNativeJointSlotEnvelopes.factor_le
    (𝓕:=𝓕) (μ:=μ) (H:=H) (Λ:=Λ) (κ:=κ) (hκ:=hκ)
      (haU:=haU) (haV:=haV) (hell:=hell) (hbU:=hbU) (hbV:=hbV) (I₀:=I₀)
      (I₁:=I₁) (u₀:=u₀) (S:=S) (P:=P) (hκP:=hκP) (J:=J)
      (hIJ₀:=hIJ₀) (hIJ₁:=hIJ₁) (hΛ:=hΛ) (hH:=hH) (h:=h) (W:=W)
      (hh:=hh) (hhP:=hhP) (hW0:=hW0) (hcover:=hcover) (hsmall:=hsmall) (Bpast:=Bpast)
      (hBDGpast:=hBDGpast) (j:=j) (r:=r) (hr:=hr) (hρ0:=(by linarith : -(1/2:ℝ)<ρ)) (hρ1:=hρhalf)
      (A:=A)
  have hroot:=MixedNativeJointSlotEnvelopes.root_le
    (𝓕:=𝓕) (μ:=μ) (H:=H) (Λ:=Λ) (κ:=κ) (hκ:=hκ)
      (haU:=haU) (haV:=haV) (hell:=hell) (hbU:=hbU) (hbV:=hbV) (I₀:=I₀)
      (I₁:=I₁) (u₀:=u₀) (S:=S) (P:=P) (hκP:=hκP) (J:=J)
      (hIJ₀:=hIJ₀) (hIJ₁:=hIJ₁) (hΛ:=hΛ) (hH:=hH) (h:=h) (W:=W)
      (hh:=hh) (hhP:=hhP) (hW0:=hW0) (hcover:=hcover) (hsmall:=hsmall) (Bpast:=Bpast)
      (hBDGpast:=hBDGpast) (ha:=ha) (hA:=hA) (hholder:=hholder) (hnull:=hnull) (B0:=B0)
      (B1:=B1) (hBDG0:=hBDG0) (hBDG1:=hBDG1) (j:=j) (r:=r) (hr:=hr)
      (Bγ:=Bγ) (hBDGγ:=hBDGγ) (hlocal:=hlocal) (Bnext:=Bnext) (hBDGnext:=hBDGnext) (hρ0:=(by linarith : -(1/2:ℝ)<ρ))
      (hρ1:=hρhalf)
  rw [hc] at he
  apply he.trans
  change 6*(ENNReal.ofReal Trace*SignedMass r+ENNReal.ofReal Higher*Factor A ρ j r+
      ENNReal.ofReal Ksum*(Direct r+Budget a j ρ 1 2 r+Budget a j ρ 3 4 r+Budget a j ρ 4 5 r))≤_
  unfold value
  gcongr
end SHE.MixedNativeJointGammaEnvelope
