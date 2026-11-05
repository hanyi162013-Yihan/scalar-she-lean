module
public import SHE.FrozenReferenceFullBand
public import SHE.HilbertBandTails
public import SHE.HilbertDyadicConvergence
public import SHE.GammaDyadicWindowScale
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
namespace SHE.FrozenReferenceFinitePrefixes
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



open Filter Real
open scoped Topology
variable (J0:ℕ)(hJH:(RemainderBandSpans.span P.exponent (J0+1):ℝ)≤H)
variable (hJP:(RemainderBandSpans.span P.exponent (J0+1):ℝ)≤P.horizon)
variable (hJG:(RemainderBandSpans.span P.exponent (J0+1):ℝ)≤NativeTwoPointCovariance.horizon)
local notation "Span" n:max=>RemainderBandSpans.span P.exponent (J0+n+1)
local notation "Width" n:max=>(H:ℝ)-(Span n:ℝ)
local notation "SpanPos" n:max=>RemainderBandSpans.span_pos P.exponent (J0+n+1)
local notation "SpanH" n:max=>(show (Span n:ℝ)≤H from
  (show (Span n:ℝ)≤(RemainderBandSpans.span P.exponent (J0+1):ℝ) by
    exact_mod_cast RemainderBandSpans.span_antitone P.exponent_pos.le (by omega : J0+1≤J0+n+1)).trans hJH)
local notation "Comp" n:max=>FrozenReferenceFullBand.completed 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
  P hκP (Width n) (Span n:ℝ) (sub_nonneg.mpr (SpanH n)) (SpanPos n)
  (show Width n+(Span n:ℝ)≤H by linarith) hH (a:=a) (J0+n) hΛ1 ρ hρ
local notation "Literal" n:max=>NativeOutputTimePatch.field (Span n) (fun _:ℝ≥0×Ω=>(0:CircleL2)) (Comp n)

include hH hF hIJ0 hIJ1 hnull hBDG0 hBDG1 ha hM0 hsmall hsmallrow
  hBDGγ hBDGpast hBDGcur hlocal hBDGnext hJ hlocalJ hK hholder hβsmall hρhalf hρeq hJH hJP hJG in
/-- Finite prefixes of the literal actual frozen terminal bands obey
one uniform RMS bound, obtained from the individual band majorants
before any infinite-series norm is taken. -/
theorem actual_prefixes :
    let α:=P.exponent+2*ρ
    let C:=NativeFrozenBesselScale.constant (2-P.exponent) κ ρ*
      (2*K*GaussianHeatBandRootEnvelope.constant P.exponent)^2
    let Cdisp:=2*((1:ℝ)+(Bnext:ℝ)*PastReferenceBracket.energyConstant P κ 1 0 1)
    let Global:=MixedMovingEnergy.globalEnergy 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
    ∃F:ℕ→ℝ≥0×Ω→CircleL2,∃hFm:∀n,Measurable (F n),
      ∃hi:∀n,Integrable (fun z=>‖F n z‖^2) (energyMeasure μ H),
      (∀n,∀ᵐt∂timeMeasure H,(fun ω=>F n (t,ω))=ᵐ[μ] (fun ω=>(Literal n) (t,ω))) ∧
      ∀L:ℕ,Integrable (fun z=>‖∑n∈Finset.range L,F n z‖^2) (energyMeasure μ H) ∧
        Real.sqrt (∫z,‖∑n∈Finset.range L,F n z‖^2 ∂energyMeasure μ H)≤
          Real.sqrt C*StateBands.rootConstant α*(Real.sqrt (Cdisp*Global))^α:=by
  intro α C Cdisp Global
  have hfamily(n:ℕ):∃Y:ℝ≥0×Ω→CircleL2,Measurable Y ∧
      (∀ᵐt∂timeMeasure H,(fun ω=>Y (t,ω))=ᵐ[μ] (fun ω=>(Literal n) (t,ω))) ∧
      Integrable (fun z=>‖Y z‖^2) (energyMeasure μ H) ∧
      (∫z,‖Y z‖^2 ∂energyMeasure μ H)≤C*CompactMollifier.radius (J0+n+1)^(2*P.exponent+4*ρ)*
        min 1 (Cdisp*Global/CompactMollifier.radius (J0+n+1)^2):=by
    have hP:(Span n:ℝ)≤P.horizon:=
      (show (Span n:ℝ)≤(RemainderBandSpans.span P.exponent (J0+1):ℝ) by
        exact_mod_cast RemainderBandSpans.span_antitone P.exponent_pos.le (by omega : J0+1≤J0+n+1)).trans hJP
    have hG:(Span n:ℝ)≤NativeTwoPointCovariance.horizon:=
      (show (Span n:ℝ)≤(RemainderBandSpans.span P.exponent (J0+1):ℝ) by
        exact_mod_cast RemainderBandSpans.span_antitone P.exponent_pos.le (by omega : J0+1≤J0+n+1)).trans hJG
    have he:(Span n:ℝ)=CompactMollifier.radius (J0+n+1)^(3*P.exponent):=by
      symm
      change CompactMollifier.radius (J0+n+1)^(3*P.exponent)=((2:ℝ)^(J0+n+1))^(-3*P.exponent)
      rw [GammaDyadicWindowScale.radius_power]
      congr 1
      ring
    have hpos:0<(Span n:ℝ):=SpanPos n
    have hout:=FrozenReferenceFullBand.exists_output
      𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P hκP
      (Width n) (Span n:ℝ) (sub_nonneg.mpr (SpanH n)) hpos (by linarith) hH
      J hF hIJ0 hIJ1 hnull B0 B1 hBDG0 hBDG1 ha hM0 (J0+n) hΛ1 ρ hρ hsmall hsmallrow
      hP hG Bγ Bpast Bcur hBDGγ hBDGpast hBDGcur hlocal Bnext hBDGnext hJ hlocalJ
      hK hholder hβsmall hρhalf hρeq he (by ring)
    simpa only [Real.toNNReal_coe] using hout
  choose F hFm hFa hi hb using hfamily
  let V:=HilbertBandTails.vector (energyMeasure μ H) F hFm hi
  let m:=Real.sqrt (Cdisp*Global)
  let R:ℝ:=(2:ℝ)^(J0+1)
  have hm:0≤m:=Real.sqrt_nonneg _
  have hR:0<R:=by dsimp [R];positivity
  have hD:0≤Cdisp:=by
    have he:=PastReferenceBracket.energyConstant_nonneg P hκP (by norm_num : (0:ℝ)≤1) 1 0
    dsimp [Cdisp]
    positivity
  have hGlobal:0≤Global:=MixedMovingEnergy.globalEnergy_nonneg 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
  have hC:0≤C:=by
    dsimp [C,NativeFrozenBesselScale.constant]
    have hmass:0<NativeGaussianCircleMass.mass (2-P.exponent) (κ/128):=
      NativeGaussianBesselCost.mass_pos (by linarith) (by positivity)
    have hg:0<Real.Gamma ρ:=Real.Gamma_pos_of_pos hρ
    have hhρ:0<1/2-ρ:=by linarith
    have hf:=NativeGaussianBesselCost.heatFactor_pos
    positivity
  have hα0:0<α:=by dsimp [α];linarith [P.exponent_pos]
  have hα1:α<1:=by dsimp [α];rw [hρeq];unfold SHE.rho;linarith [P.exponent_pos]
  have hv(n:ℕ):‖V n‖≤Real.sqrt C*((R*(2:ℝ)^n)^(-α)*min 1 (m*(R*(2:ℝ)^n))):=by
    let ν:ℝ:=(2:ℝ)^(J0+n+1)
    have hν:0<ν:=by dsimp [ν];positivity
    have hνeq:ν=R*(2:ℝ)^n:=by dsimp [ν,R];rw [show J0+n+1=J0+1+n by omega,pow_add]
    have hp:CompactMollifier.radius (J0+n+1)^(2*P.exponent+4*ρ)=(ν^(-α))^2:=by
      rw [GammaDyadicWindowScale.radius_power,←Real.rpow_mul_natCast hν.le]
      congr 1
      dsimp only [α]
      ring
    have hratio:Cdisp*Global/CompactMollifier.radius (J0+n+1)^2=(m*ν)^2:=by
      rw [GammaDyadicWindowScale.radius_inverse]
      dsimp [m,ν]
      rw [mul_pow,Real.sq_sqrt (mul_nonneg hD hGlobal)]
      field_simp
    have he:=hb n
    rw [←HilbertBandTails.vector_norm_sq (energyMeasure μ H) F hFm hi n,hp,hratio,
      ←GammaDyadicWindowScale.clipped_square (mul_nonneg hm hν.le)] at he
    have hsq:‖V n‖^2≤(Real.sqrt C*(ν^(-α)*min 1 (m*ν)))^2:=by
      rw [mul_pow,Real.sq_sqrt hC]
      convert he using 1 <;> ring
    have hn:0≤Real.sqrt C*(ν^(-α)*min 1 (m*ν)):=by positivity
    rw [←hνeq]
    nlinarith [norm_nonneg (V n)]
  have hmajor:Summable (fun n=>Real.sqrt C*((R*(2:ℝ)^n)^(-α)*min 1 (m*(R*(2:ℝ)^n)))):=
    (StateBands.scaled_root_bands hα0 hα1 hm hR).1.mul_left (Real.sqrt C)
  have hnorm:Summable (fun n=>‖V n‖):=Summable.of_nonneg_of_le (fun _=>norm_nonneg _) hv hmajor
  have htotal:(∑'n,‖V n‖)≤Real.sqrt C*StateBands.rootConstant α*m^α:=by
    calc
      _≤∑'n,Real.sqrt C*((R*(2:ℝ)^n)^(-α)*min 1 (m*(R*(2:ℝ)^n))):=
        hnorm.tsum_le_tsum hv hmajor
      _=Real.sqrt C*(∑'n,(R*(2:ℝ)^n)^(-α)*min 1 (m*(R*(2:ℝ)^n))):=tsum_mul_left
      _≤Real.sqrt C*(StateBands.rootConstant α*m^α):=
        mul_le_mul_of_nonneg_left (StateBands.scaled_root_bands hα0 hα1 hm hR).2 (Real.sqrt_nonneg C)
      _=_:=by ring
  have hrep:∀ᵐz∂energyMeasure μ H,∀n,V n z=F n z:=by
    rw [ae_all_iff]
    intro n
    exact ((memLp_two_iff_integrable_sq_norm (hFm n).aestronglyMeasurable).mpr (hi n)).coeFn_toLp
  refine ⟨F,hFm,hi,hFa,fun L=>?_⟩
  let W:Lp CircleL2 2 (energyMeasure μ H):=∑n∈Finset.range L,V n
  have he:(fun z=>W z)=ᵐ[energyMeasure μ H] (fun z=>∑n∈Finset.range L,F n z):=by
    filter_upwards [Lp.coeFn_fun_finsetSum (Finset.range L) V,hrep] with z hz hr
    exact hz.trans (Finset.sum_congr rfl (fun n _=>hr n))
  have hiW:Integrable (fun z=>‖W z‖^2) (energyMeasure μ H):=
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable W)).mp (Lp.memLp W)
  have hEq:(∫z,‖∑n∈Finset.range L,F n z‖^2 ∂energyMeasure μ H)=‖W‖^2:=by
    rw [PredictableL2.realLp_norm_sq]
    exact integral_congr_ae (he.symm.mono (fun _ hz=>congrArg (fun e:CircleL2=>‖e‖^2) hz))
  refine ⟨hiW.congr (he.mono (fun _ hz=>congrArg (fun e:CircleL2=>‖e‖^2) hz)),?_⟩
  rw [hEq,Real.sqrt_sq (norm_nonneg _)]
  exact (norm_sum_le (Finset.range L) V).trans
    ((hnorm.sum_le_tsum (Finset.range L) (fun n hn=>norm_nonneg _)).trans htotal)
end SHE.FrozenReferenceFinitePrefixes
