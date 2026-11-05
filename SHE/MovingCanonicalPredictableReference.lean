module
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
namespace SHE.MovingCanonicalPredictableReference
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
variable (I₀ I₁:StandardTerminalIto (C:=RealHaarIntegrand.Columns) (E:=RealL2) 𝓕 μ H)(u₀ v₀:RealL2)
variable (S:MixedNativeAdditiveResidualPair.Solution 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀)
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
variable (hF:StandardItoStoppedParameterFubini J)
variable (hIJ0:NativeObservationNaturality.StandardScalarNaturality I₀ (leftIntegral 𝓕 μ H J))
variable (hIJ1:NativeObservationNaturality.StandardScalarNaturality I₁ (rightIntegral 𝓕 μ H J))
variable (hnull:NullCompleteFiltration.ContainsNullSets 𝓕 μ)
variable (B0 B1:ℝ≥0)(hBDG0:StandardTerminalBDG16 I₀ B0)(hBDG1:StandardTerminalBDG16 I₁ B1)

include hW hh hcover hH hF hIJ0 hIJ1 hnull hBDG0 hBDG1 in
/-- Actual moving-past canonical reference on the ORIGINAL
past/current/root/sample product, with genuine product predictability.
All SPDE-kernel applicability is derived. The only new standard property
used is the explicitly named stopped component of stochastic Fubini4.
The equality is on the actual specified product, and original targets
and partial stops remain distinct, including q=target. -/
theorem exists_version (ν:Measure ℝ)[IsFiniteMeasure ν]:
    ∃Y:((ℝ×(ℝ≥0×Ω))×HeatCircle)→ℝ,
      @Measurable ((ℝ×(ℝ≥0×Ω))×HeatCircle) ℝ
        (((inferInstance:MeasurableSpace ℝ).prod 𝓕.predictable).prod inferInstance) _ Y ∧
      ∀ᵐr∂ν,∀ᵐq∂timeMeasure H,∀ᵐx:HeatCircle∂AddCircle.haarAddCircle,∀ᵐω∂μ,
        NativeMovingGammaClock.past W r<q→q≤NativeMovingGammaClock.terminal W h r→
          Y ((r,(q,ω)),x)=PredictableScalarField.nativeField
            (fun ω=>NativeCanonicalReferenceField.state 𝓕 μ H
              (NativeMovingGammaClock.terminal W h r) (NativeMovingGammaClock.past W r)
              P Λ κ hκ hκP (OldU r) (OldD r) (OldUM r) (OldDM r)
              (NativeMovingGammaClock.terminal_le hW hh.le H hcover r)
              ((show (NativeMovingGammaClock.terminal W h r:ℝ)≤(H:ℝ) by
                exact_mod_cast (NativeMovingGammaClock.terminal_le hW hh.le H hcover r)).trans hH)
              I₀ I₁ θ (q,ω)) (ω,x):=by
  let νp:Measure Parameters:=ν.prod ((timeMeasure H).prod AddCircle.haarAddCircle)
  obtain ⟨R,hR,hRa,hRc⟩:=MovingFrozenPredictableRows.residual_version 𝓕 μ H Λ κ hκ
    haU haV hell hbU hbV I₀ I₁ u₀ v₀ S P θ hκP W h hW hh.le hcover hH νp J hF hnull
  obtain ⟨A,hA,hAa,hAc⟩:=MovingFrozenPredictableRows.additive_version 𝓕 μ H κ hκ
    W h hW hh.le hcover hH νp J hF hnull
  let Y:((ℝ×(ℝ≥0×Ω))×HeatCircle)→ℝ:=fun z=>
    MovingFrozenInitial.scalar 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S θ W h z+
      JointPredictableDiagonal.diagonal R z+JointPredictableDiagonal.diagonal A z
  have hY:@Measurable ((ℝ×(ℝ≥0×Ω))×HeatCircle) ℝ
      (((inferInstance:MeasurableSpace ℝ).prod 𝓕.predictable).prod inferInstance) _ Y:=
    ((MovingFrozenInitial.scalar_predictable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S θ W h).add
      (JointPredictableDiagonal.predictable 𝓕 hR)).add (JointPredictableDiagonal.predictable 𝓕 hA)
  refine ⟨Y,hY,?_⟩
  filter_upwards [Measure.ae_ae_of_ae_prod hRa,Measure.ae_ae_of_ae_prod hAa] with r hr ha
  filter_upwards [Measure.ae_ae_of_ae_prod hr,Measure.ae_ae_of_ae_prod ha] with q hr ha
  by_cases hw:NativeMovingGammaClock.past W r<q∧q≤NativeMovingGammaClock.terminal W h r
  · have hbH:=NativeMovingGammaClock.terminal_le hW hh.le H hcover r
    have hb1:(NativeMovingGammaClock.terminal W h r:ℝ)≤1:=
      (show (NativeMovingGammaClock.terminal W h r:ℝ)≤(H:ℝ) by exact_mod_cast hbH).trans hH
    have hid:=CanonicalReferenceIntegral.reference_integral 𝓕 μ H
      (NativeMovingGammaClock.terminal W h r) (NativeMovingGammaClock.past W r) P Λ κ hκ hκP
      (OldU r) (OldD r) (OldUM r) (OldDM r) hbH hb1 I₀ I₁ J hIJ0 hIJ1 hnull B0 B1 hBDG0 hBDG1 θ q hw.1 hw.2
    have hii:=MovingFrozenInitialIdentity.scalar_eq 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
      θ W h r hh q hw.1
    filter_upwards [hr,ha,hid,hii] with x hr ha hid hii
    have hrq:=hr q hw.2
    have haq:=ha q hw.2
    filter_upwards [hrq,haq,hid,hii] with ω hrq haq hid hii
    intro _ _
    have hs:((NativeMovingGammaClock.terminal W h r:ℝ)-(NativeMovingGammaClock.past W r:ℝ))=h:=
      NativeMovingGammaClock.span hW hh.le r
    unfold Y JointPredictableDiagonal.diagonal
    rw [hii,hid,hs]
    rw [hrq,haq]
    rfl
  · filter_upwards [] with x
    filter_upwards [] with ω
    exact fun hv hb=>(hw ⟨hv,hb⟩).elim
end SHE.MovingCanonicalPredictableReference
