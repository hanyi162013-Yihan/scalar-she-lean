module
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
namespace SHE.FrozenReferenceFullBand
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


/-- Literal completed-window frozen term. The initial branch is zero
by the actual same-initial-data theorem InitialJointGammaFrozenZero. -/
def completed(z:ℝ≥0×Ω):CircleL2:=(Frozen (z.1:ℝ)) z.2
local notation "Completed"=>completed 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
  P hκP W h hW hh hcover hH (a:=a) j hΛ1 ρ hρ

include hW hh hcover hH hF hIJ0 hIJ1 hnull hBDG0 hBDG1 ha hM0 hsmall hsmallrow
  hwindow hsmalltime hBDGγ hBDGpast hBDGcur hlocal hBDGnext hJ hlocalJ hK hholder hβsmall hρhalf hρeq hwindoweq in
/-- Actual frozen terminal bands on the ORIGINAL full output-time
measure, with the initial zero branch retained and energy unchanged by
the physical past-to-output translation. -/
theorem exists_output (hexact:W+h=(H:ℝ)):
    let r:=CompactMollifier.radius (j+1)
    let C:=NativeFrozenBesselScale.constant (2-P.exponent) κ ρ*
      (2*K*GaussianHeatBandRootEnvelope.constant P.exponent)^2
    let Cdisp:=2*((1:ℝ)+(Bnext:ℝ)*PastReferenceBracket.energyConstant P κ 1 0 1)
    let Global:=MixedMovingEnergy.globalEnergy 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
    ∃Y:ℝ≥0×Ω→CircleL2,Measurable Y ∧
      (∀ᵐt∂timeMeasure H,(fun ω=>Y (t,ω))=ᵐ[μ]
        (fun ω=>NativeOutputTimePatch.field h.toNNReal (fun _=>0) Completed (t,ω))) ∧
      Integrable (fun z=>‖Y z‖^2) (energyMeasure μ H) ∧
      (∫z,‖Y z‖^2 ∂energyMeasure μ H)≤C*r^(2*P.exponent+4*ρ)*min 1 (Cdisp*Global/r^2):=by
  intro r C Cdisp Global
  obtain ⟨Y,hY,hYa,hYi,hYe⟩:=MovingFrozenReferenceBandEnergy.exists_output
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P hκP W h hW hh hcover hH
    J hF hIJ0 hIJ1 hnull B0 B1 hBDG0 hBDG1 ha hM0 j hΛ1 ρ hρ hsmall hsmallrow
    hwindow hsmalltime Bγ Bpast Bcur hBDGγ hBDGpast hBDGcur hlocal Bnext hBDGnext hJ hlocalJ
    hK hholder hβsmall hρhalf hρeq hwindoweq
  let hn:ℝ≥0:=h.toNNReal
  have hhn:(hn:ℝ)=h:=Real.coe_toNNReal _ hh.le
  have hhH:hn≤H:=by exact_mod_cast (show (hn:ℝ)≤(H:ℝ) by rw [hhn];linarith)
  have hWn:((H-hn:ℝ≥0):ℝ)=W:=by rw [NNReal.coe_sub hhH,hhn];linarith
  let M:ℝ≥0×Ω→CircleL2:=fun z=>Y ((z.1:ℝ),z.2)
  have hMm:Measurable M:=hY.comp ((NNReal.continuous_coe.measurable.comp measurable_fst).prodMk measurable_snd)
  have hMe:(∫⁻z,ENNReal.ofReal (‖M z‖^2) ∂energyMeasure μ (H-hn))=
      ∫⁻z,ENNReal.ofReal (‖Y z‖^2) ∂(volume.restrict (Ioc (0:ℝ) W)).prod μ:=by
    rw [energyMeasure,lintegral_prod _ ((hMm.norm.pow_const 2).ennreal_ofReal).aemeasurable,
      timeMeasure_lintegral,hWn,
      lintegral_prod _ ((hY.norm.pow_const 2).ennreal_ofReal).aemeasurable]
    apply lintegral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with z hz
    have he:(z.toNNReal:ℝ)=z:=Real.coe_toNNReal _ hz.1.le
    simp only [M,he]
  have hiM:Integrable (fun z=>‖M z‖^2) (energyMeasure μ (H-hn)):=by
    refine ⟨(hMm.norm.pow_const 2).aestronglyMeasurable,?_⟩
    rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ (fun _=>sq_nonneg _)),hMe]
    exact (hasFiniteIntegral_iff_ofReal (ae_of_all _ (fun z=>sq_nonneg ‖Y z‖))).mp hYi.hasFiniteIntegral
  have hMeR:(∫z,‖M z‖^2 ∂energyMeasure μ (H-hn))=
      ∫z,‖Y z‖^2 ∂(volume.restrict (Ioc (0:ℝ) W)).prod μ:=by
    apply (ENNReal.ofReal_eq_ofReal_iff (integral_nonneg (fun _=>sq_nonneg _))
      (integral_nonneg (fun _=>sq_nonneg _))).mp
    rw [ofReal_integral_eq_lintegral_ofReal hiM (ae_of_all _ (fun _=>sq_nonneg _)),
      ofReal_integral_eq_lintegral_ofReal hYi (ae_of_all _ (fun _=>sq_nonneg _))]
    exact hMe
  let Out:=NativeOutputTimePatch.field hn (fun _:ℝ≥0×Ω=>(0:CircleL2)) M
  have hOut:Measurable Out:=NativeOutputTimePatch.measurable hn _ M measurable_const hMm
  have he:=NativeOutputTimePatch.energy μ H hn hhH (fun _:ℝ≥0×Ω=>(0:CircleL2)) M
    measurable_const hMm (by simpa using (integrable_zero (energyMeasure μ hn))) hiM
  have hMa:∀ᵐv∂timeMeasure (H-hn),(fun ω=>M (v,ω))=ᵐ[μ] (fun ω=>Completed (v,ω)):=by
    have ha:∀ᵐz:ℝ∂volume.restrict (Ioc (0:ℝ) ((H-hn:ℝ≥0):ℝ)),
        (fun ω=>Y (z,ω))=ᵐ[μ] (Frozen z):=by simpa only [hWn] using hYa
    exact (timeMeasurePreserving (H-hn)).quasiMeasurePreserving.ae ha
  refine ⟨Out,hOut,?_,he.1,?_⟩
  · exact NativeOutputTimePatch.congr_sections μ H hn hhH (fun _=>0) M (fun _=>0) Completed
      (ae_of_all _ (fun _=>ae_of_all _ (fun _=>rfl))) hMa
  · rw [he.2]
    simp only [norm_zero,zero_pow (by decide : (2:ℕ)≠0),integral_zero,zero_add,hMeR]
    exact hYe
end SHE.FrozenReferenceFullBand
