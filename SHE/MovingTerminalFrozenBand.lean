module
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
namespace SHE.MovingTerminalFrozenBand
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

include hW hh hcover hH hF hIJ0 hIJ1 hnull hBDG0 hBDG1 ha hM0 in
/-- One Borel native Hilbert terminal-band field on the actual moving
past/sample product, identified with the literal first-pair frozen term. -/
theorem exists_version (ν:Measure ℝ)[IsFiniteMeasure ν]:
    ∃Y:ℝ×Ω→CircleL2,Measurable Y ∧
      ∀ᵐr∂ν,(fun ω=>Y (r,ω))=ᵐ[μ] (Frozen r):=by
  obtain ⟨R1,hR1,hR1a⟩:=MovingTerminalFrozenReference.exists_version
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S P 1 hκP W h hW hh hcover hH
    J hF hIJ0 hIJ1 hnull B0 B1 hBDG0 hBDG1 ν
  obtain ⟨R0,hR0,hR0a⟩:=MovingTerminalFrozenReference.exists_version
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S P 0 hκP W h hW hh hcover hH
    J hF hIJ0 hIJ1 hnull B0 B1 hBDG0 hBDG1 ν
  let F:(ℝ×Ω)×HeatCircle→ℂ:=fun z=>
    ((ScalarHeatBands.band a (j+1) (R1 z)-ScalarHeatBands.band a (j+1) (R0 z):ℝ):ℂ)
  have hbm:Measurable (ScalarHeatBands.band a (j+1)):=
    (ScalarHeatBands.band_boundedSmooth ha (j+1)).smooth.continuous.measurable
  have hFm:Measurable F:=Complex.measurable_ofReal.comp ((hbm.comp hR1).sub (hbm.comp hR0))
  have hFb(z):‖F z‖≤4*M0:=by
    have hb:=GaussianHeatBandTranslations.bounded hM0 j (R1 z) (R0 z) 0
    simpa only [F,Complex.norm_real,Real.norm_eq_abs,GaussianHeatBandTranslations.difference,zero_add] using hb
  let Y:=NativeBesselFieldAE.value Λ ρ hΛ1 hρ.le F
  have hYm:Measurable Y:=NativeBesselFieldAE.measurable Λ ρ hΛ1 hρ.le F hFm
  refine ⟨Y,hYm,?_⟩
  filter_upwards [hR1a,hR0a] with r h1 h0
  let G:Ω×HeatCircle→ℂ:=fun z=>((FrozenField r) z:ℂ)
  have hb0:=NativeMovingGammaClock.terminal_pos hW hh r
  have hGm:Measurable G:=Complex.measurable_ofReal.comp
    (JointGammaRootHilbertPair.frozenField_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV
      I₀ I₁ u₀ S P hκP (NativeMovingGammaClock.past W r) (NativeMovingGammaClock.terminal W h r)
      (NativeMovingGammaClock.terminal_le hW hh.le H hcover r) hH ha j hb0 hnull B0 B1 hBDG0 hBDG1)
  have hGbound(z):‖G z‖≤4*M0:=by
    have hb:=GaussianHeatBandTranslations.bounded hM0 j
      (NativeJointGammaFields.reference (𝓕:=𝓕) (μ:=μ) (H:=H) (v:=NativeMovingGammaClock.past W r)
        (b:=NativeMovingGammaClock.terminal W h r) (hbH:=NativeMovingGammaClock.terminal_le hW hh.le H hcover r)
        (hb1:=(show (NativeMovingGammaClock.terminal W h r:ℝ)≤(H:ℝ) by exact_mod_cast
          (NativeMovingGammaClock.terminal_le hW hh.le H hcover r)).trans hH)
        (U:=Function.uncurry S.first) (V:=Function.uncurry S.second) (hU:=S.first_predictable)
        (hV:=S.second_predictable) (P:=P) (Λ:=Λ) (κ:=κ) (hκ:=hκ) (hκP:=hκP) (I0:=I₀) (I1:=I₁) 1
        ((NativeMovingGammaClock.terminal W h r,z.1),z.2))
      (NativeJointGammaFields.reference (𝓕:=𝓕) (μ:=μ) (H:=H) (v:=NativeMovingGammaClock.past W r)
        (b:=NativeMovingGammaClock.terminal W h r) (hbH:=NativeMovingGammaClock.terminal_le hW hh.le H hcover r)
        (hb1:=(show (NativeMovingGammaClock.terminal W h r:ℝ)≤(H:ℝ) by exact_mod_cast
          (NativeMovingGammaClock.terminal_le hW hh.le H hcover r)).trans hH)
        (U:=Function.uncurry S.first) (V:=Function.uncurry S.second) (hU:=S.first_predictable)
        (hV:=S.second_predictable) (P:=P) (Λ:=Λ) (κ:=κ) (hκ:=hκ) (hκP:=hκP) (I0:=I₀) (I1:=I₁) 0
        ((NativeMovingGammaClock.terminal W h r,z.1),z.2)) 0
    simpa only [G,Complex.norm_real,Real.norm_eq_abs,JointGammaRootHilbertPair.frozenField,
      GaussianHeatBandTranslations.difference,zero_add] using hb
  let Fr:Ω×HeatCircle→ℂ:=fun z=>F ((r,z.1),z.2)
  have hFrm:Measurable Fr:=hFm.comp ((measurable_const.prodMk measurable_fst).prodMk measurable_snd)
  have hEq:∀ᵐx:HeatCircle∂AddCircle.haarAddCircle,∀ᵐω∂μ,Fr (ω,x)=G (ω,x):=by
    filter_upwards [h1,h0] with x h1 h0
    filter_upwards [h1,h0] with ω h1 h0
    change (((ScalarHeatBands.band a (j+1) (R1 ((r,ω),x))-
      ScalarHeatBands.band a (j+1) (R0 ((r,ω),x))):ℝ):ℂ)=G (ω,x)
    rw [h1,h0]
    rfl
  have hEvt:MeasurableSet {z:Ω×HeatCircle|Fr z=G z}:=measurableSet_eq_fun hFrm hGm
  have he:∀ᵐω∂μ,∀ᵐx:HeatCircle∂AddCircle.haarAddCircle,Fr (ω,x)=G (ω,x):=
    (Measure.ae_ae_comm hEvt).mpr hEq
  filter_upwards [he] with ω hω
  have hmemF:MemLp (fun x=>Fr (ω,x)) 2 AddCircle.haarAddCircle:=
    MemLp.of_bound (hFrm.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
      (4*M0) (ae_of_all _ (fun x=>hFb ((r,ω),x)))
  have hmemG:MemLp (fun x=>G (ω,x)) 2 AddCircle.haarAddCircle:=
    MemLp.of_bound (hGm.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
      (4*M0) (ae_of_all _ (fun x=>hGbound (ω,x)))
  exact NativeBesselSectionEnergy.congr Λ ρ hΛ1 hρ.le Fr G hFrm hGm ω hmemF hmemG hω
end SHE.MovingTerminalFrozenBand
