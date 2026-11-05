module
public import SHE.FrozenReferenceFullBand
public import SHE.InitialJointGammaFrozenZero
public import SHE.MovingFrozenReferenceBandEnergy
public import SHE.NativeOutputTimePatch
public import SHE.MovingTerminalFrozenBand
public import SHE.MixedNativePastBudget
public import SHE.MovingTerminalFrozenReference
public import SHE.JointGammaFrozenBandEnergy
public import SHE.NativeBesselSectionEnergy
public import SHE.MovingFrozenPredictableRows
public import SHE.MovingFrozenInitialIdentity
public import SHE.JointPredictableDiagonal
public import SHE.CanonicalReferenceIntegral
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
namespace SHE.FrozenReferenceFullIdentity
open Set MeasureTheory PredictableL2 FiniteHaar StoppedFourier NativeHeatObservation
open OrthogonalItoChannels DyadicApproximation MovingCanonicalFrozenRows
open scoped NNReal ENNReal
local instance movingCanonicalPredictableReference_unit : Fact (0<(1:ℝ)):=⟨zero_lt_one⟩
local instance movingCanonicalPredictableReference_period : Fact (0<2*Real.pi):=⟨by positivity⟩
local instance movingCanonicalPredictableReference_realSigma : MeasurableSpace RealL2:=borel _
local instance movingCanonicalPredictableReference_realBorel : BorelSpace RealL2:=⟨rfl⟩
local instance movingCanonicalPredictableReference_realSecond : SecondCountableTopology RealL2:=
  realCircleIdentification.toHomeomorph.secondCountableTopology
local instance movingCanonicalPredictableReference_circleSigma : MeasurableSpace CircleL2:=borel _
local instance movingCanonicalPredictableReference_circleBorel : BorelSpace CircleL2:=⟨rfl⟩
local instance movingCanonicalPredictableReference_rowSigma : MeasurableSpace RealHaarInput:=borel _
local instance movingCanonicalPredictableReference_rowBorel : BorelSpace RealHaarInput:=⟨rfl⟩
local instance movingCanonicalPredictableReference_bothSigma : MeasurableSpace (Both RealHaarInput):=borel _
local instance movingCanonicalPredictableReference_bothBorel : BorelSpace (Both RealHaarInput):=⟨rfl⟩
variable {Ω:Type}[MeasurableSpace Ω]
variable (𝓕:Filtration ℝ≥0 ‹MeasurableSpace Ω›)(μ:Measure Ω)[IsProbabilityMeasure μ](H:ℝ≥0)
variable (Λ κ:ℝ)(hκ:0<κ){aU aV:ℝ→ℝ}(haU:Measurable aU)(haV:Measurable aV){ell M:ℝ}
variable (hell:0<ell)(hbU:∀z,ell≤aU z∧aU z≤M)(hbV:∀z,ell≤aV z∧aV z≤M)
variable (I₀ I₁:StandardTerminalIto (C:=RealHaarIntegrand.Columns) (E:=RealL2) 𝓕 μ H)(u₀:RealL2)
variable (S:MixedNativeAdditiveResidualPair.Solution 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀)
variable (P:CanonicalCovariance.ProfileParameters)(θ:ℝ)(hκP:κ<P.lower)(W h:ℝ)
local notation "OldU" r=>S.first (NativeMovingGammaClock.past W r)
local notation "OldD" r=>(fun ω=>S.second (NativeMovingGammaClock.past W r) ω-S.first (NativeMovingGammaClock.past W r) ω)
local notation "OldUM" r=>(((show IsStronglyPredictable 𝓕 S.first from S.first_predictable).stronglyAdapted
  (NativeMovingGammaClock.past W r)).measurable)
local notation "OldDM" r=>((((show IsStronglyPredictable 𝓕 S.second from S.second_predictable).stronglyAdapted
  (NativeMovingGammaClock.past W r)).sub
  ((show IsStronglyPredictable 𝓕 S.first from S.first_predictable).stronglyAdapted
  (NativeMovingGammaClock.past W r))).measurable)
variable (hW:0≤W)(hh:0<h)(hcover:W+h≤H)(hH:(H:ℝ)≤1)
variable (J:StandardTerminalIto (C:=Both RealHaarInput) (E:=ℝ) 𝓕 μ H)
variable (hF:StandardItoParameterFubini J)
variable (hIJ0:NativeObservationNaturality.StandardScalarNaturality I₀ (leftIntegral 𝓕 μ H J))
variable (hIJ1:NativeObservationNaturality.StandardScalarNaturality I₁ (rightIntegral 𝓕 μ H J))
variable (hnull:NullCompleteFiltration.ContainsNullSets 𝓕 μ)
variable (B0 B1:ℝ≥0)(hBDG0:StandardTerminalBDG16 I₀ B0)(hBDG1:StandardTerminalBDG16 I₁ B1)



local instance movingTerminalFrozenBand_second : SecondCountableTopology CircleL2:=
  (_root_.fourierBasis (T:=2*Real.pi)).repr.toHomeomorph.secondCountableTopology
variable {a:ℝ→ℝ}(ha:SmoothCylinders.BoundedSmooth a){M0:ℝ}(hM0:∀z,|a z|≤M0)
variable (j:ℕ)(hΛ1:1≤Λ)(ρ:ℝ)(hρ:0<ρ)
local notation "FrozenField" r:max=>JointGammaRootHilbertPair.frozenField 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
  P hκP (NativeMovingGammaClock.past W r) (NativeMovingGammaClock.terminal W h r)
  (NativeMovingGammaClock.terminal_le hW hh.le H hcover r) hH (a:=a) j
local notation "Frozen" r:max=>JointGammaRootHilbertPair.frozen 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
  P hκP (NativeMovingGammaClock.past W r) (NativeMovingGammaClock.terminal W h r)
  (NativeMovingGammaClock.terminal_le hW hh.le H hcover r) hH (a:=a) j hΛ1 hρ


variable (hsmall:ProfileStability.memoryConstant P.lower P.holder P.exponent*
  ProfileVolterra.powerConstant ((P.exponent-1)/4)*P.horizon^(P.exponent/4)≤1/2)
variable (hsmallrow:ProfileStability.memoryConstant P.lower P.holder P.exponent*
  ProfileVolterra.powerConstant ((P.exponent-2)/4)*P.horizon^(P.exponent/4)≤1/2)
variable (hwindow:h≤P.horizon)(hsmalltime:h≤NativeTwoPointCovariance.horizon)
variable (Bγ Bpast Bcur:ℝ≥0)(hBDGγ:StandardTerminalBDG16 J Bγ)
variable (hBDGpast:StandardTerminalBDGPower 2 J Bpast)(hBDGcur:StandardTerminalBDGPower 1 J Bcur)
variable (hlocal:StandardTerminalPastLocality I₁)(Bnext:ℝ≥0)(hBDGnext:StandardTerminalBDGPower 1 I₁ Bnext)
variable (hJ:StandardFiniteIto.Universal 𝓕 μ H J)(hlocalJ:StandardTerminalPastLocality J)
variable {K:ℝ}(hK:0≤K)(hholder:∀z w,|a z-a w|≤K*|z-w|^P.exponent)
variable (hβsmall:P.exponent≤4/25)(hρhalf:ρ<1/2)(hρeq:ρ=SHE.rho P.exponent)
variable (hwindoweq:h=CompactMollifier.radius (j+1)^(3*P.exponent))



/-- Actual first-pair frozen field at the original terminal and the
clipped past. Its total extension clips only outside the original H. -/
def original(z:ℝ≥0×Ω):CircleL2:=
  JointGammaRootHilbertPair.frozen 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P hκP
    (min z.1 H-h.toNNReal) (min z.1 H) (min_le_right _ _) hH (a:=a) j hΛ1 hρ z.2
local notation "Original"=>original 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P hκP h hH (a:=a) j hΛ1 ρ hρ
local notation "Completed"=>FrozenReferenceFullBand.completed 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
  P hκP W h hW hh hcover hH (a:=a) j hΛ1 ρ hρ

include hW hh hcover hH hIJ0 hIJ1 hnull hBDG0 hBDG1 ha hsmall hwindow hBDGγ hBDGpast hlocal hBDGnext in
/-- Exact ALL-time frozen reference attachment, including its genuine
initial zero strip and every completed-window terminal/past clock. -/
theorem identity_ae(hexact:W+h=(H:ℝ)):
    ∀ᵐt∂timeMeasure H,(fun ω=>NativeOutputTimePatch.field h.toNNReal (fun _=>0) Completed (t,ω))=ᵐ[μ]
      (fun ω=>Original (t,ω)):=by
  have hhn:(h.toNNReal:ℝ)=h:=Real.coe_toNNReal _ hh.le
  filter_upwards [timeMeasure_ae_mem H] with t ht
  have hbt:min t H=t:=min_eq_left ht.2
  by_cases hth:t≤h.toNNReal
  · have hz:=InitialJointGammaFrozenZero.frozen_zero
      𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S J P hκP
      (zero_le_one.trans hΛ1) t ht.2 hH Bγ hBDGγ hIJ0 hIJ1 ht.1 hnull B0 B1 hBDG0 hBDG1
      hsmall Bpast hBDGpast hlocal Bnext hBDGnext a j ha hΛ1 hρ
      ((show (t:ℝ)≤h from by simpa only [hhn] using NNReal.coe_le_coe.mpr hth).trans hwindow)
    filter_upwards [hz] with ω hω
    simp only [NativeOutputTimePatch.field,if_pos hth,original,hbt,
      tsub_eq_zero_of_le hth]
    exact hω.symm
  · have hlt:h.toNNReal<t:=lt_of_not_ge hth
    have hle:h.toNNReal≤t:=hlt.le
    have hr:((t-h.toNNReal:ℝ≥0):ℝ)∈Ioc (0:ℝ) W:=by
      rw [NNReal.coe_sub hle,hhn]
      refine ⟨?_,?_⟩
      · have hh':(h.toNNReal:ℝ)<(t:ℝ):=by exact_mod_cast hlt
        linarith
      · have htH:(t:ℝ)≤(H:ℝ):=by exact_mod_cast ht.2
        linarith
    have hv:NativeMovingGammaClock.past W ((t-h.toNNReal:ℝ≥0):ℝ)=t-h.toNNReal:=by
      rw [NativeMovingGammaClock.past_eq hr,Real.toNNReal_coe]
    have hb:NativeMovingGammaClock.terminal W h ((t-h.toNNReal:ℝ≥0):ℝ)=t:=by
      rw [NativeMovingGammaClock.terminal_eq hr]
      apply NNReal.coe_injective
      change (((((t-h.toNNReal:ℝ≥0):ℝ)+h).toNNReal):ℝ)=(t:ℝ)
      rw [Real.coe_toNNReal _ (add_nonneg (NNReal.coe_nonneg _) hh.le),NNReal.coe_sub hle,hhn]
      ring
    filter_upwards with ω
    simp only [NativeOutputTimePatch.field,if_neg hth,FrozenReferenceFullBand.completed,
      original,hbt,hv,hb]
end SHE.FrozenReferenceFullIdentity
