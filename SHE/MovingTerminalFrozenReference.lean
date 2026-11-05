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
namespace SHE.MovingTerminalFrozenReference
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
variable (hF:StandardItoParameterFubini J)
variable (hIJ0:NativeObservationNaturality.StandardScalarNaturality I₀ (leftIntegral 𝓕 μ H J))
variable (hIJ1:NativeObservationNaturality.StandardScalarNaturality I₁ (rightIntegral 𝓕 μ H J))
variable (hnull:NullCompleteFiltration.ContainsNullSets 𝓕 μ)
variable (B0 B1:ℝ≥0)(hBDG0:StandardTerminalBDG16 I₀ B0)(hBDG1:StandardTerminalBDG16 I₁ B1)


include hW hh hcover hH hF hIJ0 hIJ1 hnull hBDG0 hBDG1 in
/-- Genuine moving TERMINAL reference version. The stochastic parameter
measure is placed on q=terminal before Fubini, rather than evaluating
an almost-every-current-time version on that diagonal. -/
theorem exists_version (ν:Measure ℝ)[IsFiniteMeasure ν]:
    ∃Y:(ℝ×Ω)×HeatCircle→ℝ,Measurable Y ∧
      ∀ᵐr∂ν,∀ᵐx:HeatCircle∂AddCircle.haarAddCircle,∀ᵐω∂μ,
        Y ((r,ω),x)=PredictableScalarField.nativeField
          (fun ω=>NativeCanonicalReferenceField.state 𝓕 μ H
            (NativeMovingGammaClock.terminal W h r) (NativeMovingGammaClock.past W r)
            P Λ κ hκ hκP (OldU r) (OldD r) (OldUM r) (OldDM r)
            (NativeMovingGammaClock.terminal_le hW hh.le H hcover r)
            ((show (NativeMovingGammaClock.terminal W h r:ℝ)≤(H:ℝ) by
              exact_mod_cast (NativeMovingGammaClock.terminal_le hW hh.le H hcover r)).trans hH)
            I₀ I₁ θ (NativeMovingGammaClock.terminal W h r,ω)) (ω,x):=by
  let liftX:ℝ×HeatCircle→Parameters:=fun z=>(z.1,(NativeMovingGammaClock.terminal W h z.1,z.2))
  have hlm:Measurable liftX:=measurable_fst.prodMk
    (((NativeMovingGammaClock.terminal_measurable W h).comp measurable_fst).prodMk measurable_snd)
  have hli:Function.Injective liftX:=by
    intro x y hxy
    have h1:x.1=y.1:=congrArg (fun z:Parameters=>z.1) hxy
    have h2:x.2=y.2:=congrArg (fun z:Parameters=>z.2.2) hxy
    exact Prod.ext h1 h2
  have hl:MeasurableEmbedding liftX:=hlm.measurableEmbedding hli
  let νp:Measure Parameters:=Measure.map liftX (ν.prod AddCircle.haarAddCircle)
  obtain ⟨R,hR,hRa,hRe,hRb,hRf⟩:=MovingCanonicalFrozenRows.residual_version
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S P θ hκP W h
    hW hh.le hcover hH νp J hF
  obtain ⟨A,hA,hAa,hAe,hAb,hAf⟩:=MovingCanonicalFrozenRows.additive_version
    (𝓕:=𝓕) (μ:=μ) (H:=H) (κ:=κ) (hκ:=hκ) (W:=W) (h:=h)
    (hW:=hW) (hh:=hh.le) (hcover:=hcover) (hH:=hH) νp J hF
  have hRa':∀ᵐz:ℝ×HeatCircle∂ν.prod AddCircle.haarAddCircle,
      (fun ω=>R (liftX z,ω))=ᵐ[μ] (rightIntegral 𝓕 μ H J).integral
        (ParametricStoppedHaarRows.process 𝓕 μ H (sub_pos.mpr hκP)
          (PastFrozenPrefixRows.residual_upper_nonneg P κ hκP)
          (past W) (terminal W h) (current W h) center
          (MovingCanonicalFrozenRows.field 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S P θ hκP W)
          (MovingCanonicalFrozenRows.field_predictable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S P θ hκP W)
          (current_le W h) (fun z=>NativeMovingGammaClock.terminal_le hW hh.le H hcover z.1) (liftX z)):=
    hl.ae_map_iff.mp hRa
  have hAa':=hl.ae_map_iff.mp hAa
  let Y:(ℝ×Ω)×HeatCircle→ℝ:=fun z=>
    MovingFrozenInitial.scalar 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S θ W h
      ((z.1.1,(NativeMovingGammaClock.terminal W h z.1.1,z.1.2)),z.2)+
        R (liftX (z.1.1,z.2),z.1.2)+A (liftX (z.1.1,z.2),z.1.2)
  have hIm:Measurable (MovingFrozenInitial.scalar 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S θ W h):=by
    have hi:@Measurable ((ℝ×(ℝ≥0×Ω))×HeatCircle) ((ℝ×(ℝ≥0×Ω))×HeatCircle) _
        (((inferInstance:MeasurableSpace ℝ).prod 𝓕.predictable).prod inferInstance) id:=
      (measurable_fst.fst.prodMk (measurable_fst.snd.mono le_rfl (predictable_le_product 𝓕))).prodMk measurable_snd
    exact (MovingFrozenInitial.scalar_predictable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S θ W h).comp hi
  have hY:Measurable Y:=by
    have hi:=hIm.comp ((measurable_fst.fst.prodMk
      (((NativeMovingGammaClock.terminal_measurable W h).comp measurable_fst.fst).prodMk measurable_fst.snd)).prodMk measurable_snd)
    have hm:Measurable (fun z:(ℝ×Ω)×HeatCircle=>(liftX (z.1.1,z.2),z.1.2)):=
      (hlm.comp (measurable_fst.fst.prodMk measurable_snd)).prodMk measurable_fst.snd
    exact (hi.add (hR.comp hm)).add (hA.comp hm)
  refine ⟨Y,hY,?_⟩
  filter_upwards [Measure.ae_ae_of_ae_prod hRa',Measure.ae_ae_of_ae_prod hAa'] with r hr ha
  have hvb:=NativeMovingGammaClock.past_lt hW hh r
  have hbH:=NativeMovingGammaClock.terminal_le hW hh.le H hcover r
  have hb1:(NativeMovingGammaClock.terminal W h r:ℝ)≤1:=
    (show (NativeMovingGammaClock.terminal W h r:ℝ)≤(H:ℝ) by exact_mod_cast hbH).trans hH
  have hid:=CanonicalReferenceIntegral.reference_integral 𝓕 μ H
    (NativeMovingGammaClock.terminal W h r) (NativeMovingGammaClock.past W r) P Λ κ hκ hκP
    (OldU r) (OldD r) (OldUM r) (OldDM r) hbH hb1 I₀ I₁ J hIJ0 hIJ1 hnull B0 B1 hBDG0 hBDG1
    θ (NativeMovingGammaClock.terminal W h r) hvb le_rfl
  have hii:=MovingFrozenInitialIdentity.scalar_eq 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
    θ W h r hh (NativeMovingGammaClock.terminal W h r) hvb
  have hspan:=NativeMovingGammaClock.span hW hh.le r
  filter_upwards [hr,ha,hid,hii] with x hr ha hid hii
  have hcurr:current W h (liftX (r,x))=NativeMovingGammaClock.terminal W h r:=
    current_eq (liftX (r,x)) hvb.le le_rfl
  simp only [ParametricStoppedHaarRows.process,hcurr] at hr ha
  filter_upwards [hr,ha,hid,hii] with ω hr ha hid hii
  dsimp only [Y]
  rw [hii,hid,hspan]
  rw [hr,ha]
  rfl
end SHE.MovingTerminalFrozenReference
