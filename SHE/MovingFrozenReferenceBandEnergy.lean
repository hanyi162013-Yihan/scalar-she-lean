module
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
namespace SHE.MovingFrozenReferenceBandEnergy
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

include hW hh hcover hH hF hIJ0 hIJ1 hnull hBDG0 hBDG1 ha hM0 hsmall hsmallrow
  hwindow hsmalltime hBDGγ hBDGpast hBDGcur hlocal hBDGnext hJ hlocalJ hK hholder hβsmall hρhalf hρeq hwindoweq in
/-- The literal moving first-pair frozen band, with a genuine common
Borel Hilbert version and its sharp global clipped energy. -/
theorem exists_output :
    let ν:=volume.restrict (Ioc (0:ℝ) W)
    let r:=CompactMollifier.radius (j+1)
    let C:=NativeFrozenBesselScale.constant (2-P.exponent) κ ρ*
      (2*K*GaussianHeatBandRootEnvelope.constant P.exponent)^2
    let Cdisp:=2*((1:ℝ)+(Bnext:ℝ)*PastReferenceBracket.energyConstant P κ 1 0 1)
    let Global:=MixedMovingEnergy.globalEnergy 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
    ∃Y:ℝ×Ω→CircleL2,Measurable Y ∧
      (∀ᵐr∂ν,(fun ω=>Y (r,ω))=ᵐ[μ] (Frozen r)) ∧
      Integrable (fun z=>‖Y z‖^2) (ν.prod μ) ∧
      (∫z,‖Y z‖^2 ∂ν.prod μ)≤C*r^(2*P.exponent+4*ρ)*min 1 (Cdisp*Global/r^2):=by
  intro ν r C Cdisp Global
  obtain ⟨Y,hY,hYa⟩:=MovingTerminalFrozenBand.exists_version
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P hκP W h hW hh hcover hH
    J hF hIJ0 hIJ1 hnull B0 B1 hBDG0 hBDG1 ha hM0 j hΛ1 ρ hρ ν
  have hC:0≤C:=by
    dsimp [C,NativeFrozenBesselScale.constant]
    have hm:0<NativeGaussianCircleMass.mass (2-P.exponent) (κ/128):=
      NativeGaussianBesselCost.mass_pos (by linarith) (by positivity)
    have hg:0<Real.Gamma ρ:=Real.Gamma_pos_of_pos hρ
    have hhρ:0<1/2-ρ:=by linarith
    have hf:=NativeGaussianBesselCost.heatFactor_pos
    positivity
  have hD:0≤Cdisp:=by
    have he:=PastReferenceBracket.energyConstant_nonneg P hκP (by norm_num : (0:ℝ)≤1) 1 0
    dsimp [Cdisp]
    positivity
  have hWle:W≤H:=by linarith
  let G:ℝ→ℝ≥0∞:=fun z=>∫⁻ω,ENNReal.ofReal (‖(Frozen z) ω‖^2) ∂μ
  have hG(z:ℝ)(hz:z∈Ioc (0:ℝ) W):G z≤
      ENNReal.ofReal (C*r^(2*P.exponent+4*ρ)*min 1
        (Cdisp*(∫ω,‖S.second z.toNNReal ω-S.first z.toNNReal ω‖^2 ∂μ)/r^2)):=by
    have hvb:=NativeMovingGammaClock.past_lt hW hh z
    have hbH:=NativeMovingGammaClock.terminal_le hW hh.le H hcover z
    have hspan:=NativeMovingGammaClock.span hW hh.le z
    have he:=JointGammaFrozenBandEnergy.energy 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
      J P hκP (NativeMovingGammaClock.past W z) hH Bγ hBDGγ hIJ0 hIJ1 hsmall Bpast hBDGpast
      (NativeMovingGammaClock.terminal W h z) hvb hbH (by rw [hspan];exact hwindow)
      hsmallrow (by rw [hspan];exact hsmalltime) hΛ1 ρ hρ hρhalf hnull B0 B1 hBDG0 hBDG1
      hlocal Bnext hBDGnext hJ hlocalJ ha hM0 hK P.exponent_pos.le (by linarith) hholder j
      P.exponent_pos hβsmall hρeq (by rw [hspan];exact hwindoweq)
    dsimp only at he
    dsimp only [G]
    rw [←ofReal_integral_eq_lintegral_ofReal he.1 (ae_of_all _ (fun _=>sq_nonneg _))]
    apply ENNReal.ofReal_le_ofReal
    simpa only [NativeMovingGammaClock.past_eq hz,C,Cdisp,r] using he.2
  have hcap:=MixedNativePastBudget.clipped 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
    J hIJ0 hIJ1 (zero_le_one.trans hΛ1) hH Bcur hBDGcur hW hWle
    (mul_nonneg hC (Real.rpow_nonneg (CompactMollifier.radius_pos _).le _)) hD
    (CompactMollifier.radius_pos (j+1)) G hG
  have hlin:(∫⁻z,ENNReal.ofReal (‖Y z‖^2) ∂ν.prod μ)≤
      ENNReal.ofReal (C*r^(2*P.exponent+4*ρ)*min 1 (Cdisp*Global/r^2)):=by
    calc
      _=(∫⁻z,∫⁻ω,ENNReal.ofReal (‖Y (z,ω)‖^2) ∂μ ∂ν):=
        lintegral_prod _ ((hY.norm.pow_const 2).ennreal_ofReal).aemeasurable
      _=∫⁻z,G z ∂ν:=by
        apply lintegral_congr_ae
        filter_upwards [hYa] with z hz
        exact lintegral_congr_ae (hz.mono (fun ω hω=>congrArg (fun z:CircleL2=>ENNReal.ofReal (‖z‖^2)) hω))
      _≤_:=hcap
  have hi:Integrable (fun z=>‖Y z‖^2) (ν.prod μ):=
    ⟨(hY.norm.pow_const 2).aestronglyMeasurable,
      (hasFiniteIntegral_iff_ofReal (ae_of_all _ (fun _=>sq_nonneg _))).mpr
        (hlin.trans_lt ENNReal.ofReal_lt_top)⟩
  refine ⟨Y,hY,hYa,hi,?_⟩
  rw [←ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ (fun _=>sq_nonneg _))] at hlin
  apply (ENNReal.ofReal_le_ofReal_iff _).mp hlin
  exact mul_nonneg (mul_nonneg hC (Real.rpow_nonneg (CompactMollifier.radius_pos _).le _))
    (le_min zero_le_one (div_nonneg (mul_nonneg hD (MixedMovingEnergy.globalEnergy_nonneg
      𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S)) (sq_nonneg r)))
end SHE.MovingFrozenReferenceBandEnergy
