module

public import SHE.NativeFrozenReferenceBesselEnergy
public import SHE.ClippedDisplacementEnergy
public import SHE.FirstGammaTerminalReferenceEnergy
public import SHE.FirstGammaCanonicalReferenceEnergy
public import SHE.NativeRepresentativeEnergy
public import SHE.ConditionalFatouMoment
public import Mathlib.Topology.Order.IsLUB
public import SHE.FirstGammaReferenceEnergy
public import SHE.FirstGammaCanonicalReference
public import SHE.FirstGammaEndpointReferenceHilbert
public import SHE.NativeCanonicalGammaFields
public import SHE.JointInterpolationFields

@[expose] public section
noncomputable section

set_option autoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2300000

namespace SHE.FirstGammaTerminalReferenceBessel
open MeasureTheory AddCircle GaussianIncrement NativeHeatObservation NativeObservationNaturality
open FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation PredictableL2
open scoped NNReal ENNReal Topology
open Filter
local instance firstGammaReferenceEnergy_period : Fact (0<2*Real.pi):=⟨by positivity⟩
local instance firstGammaFrozenValues_realSigma : MeasurableSpace RealL2 := borel _
local instance firstGammaFrozenValues_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance firstGammaFrozenValues_circleSigma : MeasurableSpace CircleL2 := borel _
local instance firstGammaFrozenValues_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩
local instance firstGammaFrozenValues_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance firstGammaFrozenValues_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance firstGammaFrozenValues_blockSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance firstGammaFrozenValues_blockBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
variable {Ω : Type*} [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
variable (Λ κ : ℝ) (hκ : 0<κ) {aU aV : ℝ→ℝ} (haU : Measurable aU) (haV : Measurable aV) {ell M : ℝ}
variable (hell : 0<ell) (hbU : ∀ z,ell≤aU z ∧ aU z≤M) (hbV : ∀ z,ell≤aV z ∧ aV z≤M)
variable (I₀ I₁ : StandardTerminalIto (C := RealHaarIntegrand.Columns) (E := RealL2) 𝓕 μ H)
variable (u₀ : RealL2)
variable (S : MixedNativeAdditiveResidualPair.Solution 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀)
variable {n : ℕ} (Z : Fin n→WordRecursion.Observation)



variable (J : StandardTerminalIto (C:=Both RealHaarInput) (E:=ℝ) 𝓕 μ H)
variable (P : CanonicalCovariance.ProfileParameters) (hκP : κ<P.lower)
variable (hΛ : 0≤Λ) (v c : ℝ≥0) (hgap : ∀ i,(c:ℝ)<(Z i).target)


open FirstGammaConstruction
local notation "Rold" => FirstGammaRows.actual 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S Z hΛ c hgap
local notation "Rnew" => FirstGammaRows.replacement 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S Z P hκP v c hgap
local notation "z₀" => MixedNativePairExtendedMartingale.initial u₀ u₀ (fun i=>(Z i).target) (fun i=>(Z i).center)
local notation "Y" => FirstGammaConstruction.value 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S Z J P hκP hΛ v c hgap
variable (hH : (H:ℝ)≤1) (hH0 : 0<H) (B : ℝ≥0) (hBDG : StandardTerminalBDG16 J B)
variable (hIJ₀ : StandardScalarNaturality I₀ (leftIntegral 𝓕 μ H J))
variable (hIJ₁ : StandardScalarNaturality I₁ (rightIntegral 𝓕 μ H J))



local notation "Data"=>MixedPastReference.data 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S v
local notation "DataM"=>MixedPastReference.data_past_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S v
variable (hsmall:ProfileStability.memoryConstant P.lower P.holder P.exponent*
  ProfileVolterra.powerConstant ((P.exponent-1)/4)*P.horizon^(P.exponent/4)≤1/2)
variable (hvc:v<c) (hcH:c≤H) (hspan:(c:ℝ)-(v:ℝ)≤P.horizon)
variable (Bpast:ℝ≥0) (hBDGpast:StandardTerminalBDGPower 2 J Bpast)
local notation "hv1"=>(show (v:ℝ)≤1 from
  (show (v:ℝ)≤(H:ℝ) from by exact_mod_cast hvc.le.trans hcH).trans hH)
local notation "Inp" "[" θ "," η "]"=>MixedPastReference.input
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S J hIJ₀ hIJ₁
  P hΛ hκP θ η hsmall v c hvc hcH hv1 hspan 1 (by norm_num) Bpast hBDGpast



local notation "OldU"=>S.first v
local notation "OldD"=>(fun ω=>S.second v ω-S.first v ω)
local notation "OldUM"=>(((show IsStronglyPredictable 𝓕 S.first from S.first_predictable).stronglyAdapted v).measurable)
local notation "OldDM"=>((((show IsStronglyPredictable 𝓕 S.second from S.second_predictable).stronglyAdapted v).sub
  ((show IsStronglyPredictable 𝓕 S.first from S.first_predictable).stronglyAdapted v)).measurable)


local notation "Field" b:max hbH:max ξ:max=>NativeFrozenReferenceBand.field 𝓕 μ H b v P Λ κ hκ hκP
  OldU OldD OldUM OldDM hbH ((show (b:ℝ)≤(H:ℝ) by exact_mod_cast hbH).trans hH) I₀ I₁ ξ
local notation "Y" b:max hbH:max ρ:max hΛ1:max hρ:max a:max j:max θ:max η:max=>
  NativeFrozenReferenceBesselEnergy.value 𝓕 μ H b v P Λ κ hκ hκP
    OldU OldD OldUM OldDM hbH ((show (b:ℝ)≤(H:ℝ) by exact_mod_cast hbH).trans hH)
    I₀ I₁ ρ hΛ1 hρ a j θ η
local notation "Scaled" b:max hbH:max K:max β:max j:max θ:max η:max=>
  NativeFrozenReferenceCovarianceKernel.scaledAmplitude 𝓕 μ H b v P Λ κ hκ hκP
    OldU OldD OldUM OldDM hbH ((show (b:ℝ)≤(H:ℝ) by exact_mod_cast hbH).trans hH)
    I₀ I₁ K β j θ η

include hIJ₀ hIJ₁ hH hsmall Bpast hBDGpast B hBDG in
/-- The actual compatible frozen terminal band, on the original sample
space, gains its native Bessel spatial factor and keeps the true clipped
past displacement. No terminal law or energy premise is supplied. -/
theorem energy (b:ℝ≥0) (hvb:v<b)(hbH:b≤H)
    (hwindow:(b:ℝ)-(v:ℝ)≤P.horizon)
    (hsmallrow:ProfileStability.memoryConstant P.lower P.holder P.exponent*
      ProfileVolterra.powerConstant ((P.exponent-2)/4)*P.horizon^(P.exponent/4)≤1/2)
    (hsmalltime:(b:ℝ)-(v:ℝ)≤NativeTwoPointCovariance.horizon)
    (hΛ1:1≤Λ)(ρ:ℝ)(hρ:0<ρ)(hρhalf:ρ<1/2)
    (hnull:NullCompleteFiltration.ContainsNullSets 𝓕 μ)
    (B0 B1:ℝ≥0)(hBDG0:StandardTerminalBDG16 I₀ B0)(hBDG1:StandardTerminalBDG16 I₁ B1)
    (hlocal:StandardTerminalPastLocality I₁)(Bnext:ℝ≥0)
    (hBDGnext:StandardTerminalBDGPower 1 I₁ Bnext)
    (hJ:StandardFiniteIto.Universal 𝓕 μ H J)(hlocalJ:StandardTerminalPastLocality J)
    (θ η:ℝ){a:ℝ→ℝ}(ha:SmoothCylinders.BoundedSmooth a){M0 K β:ℝ}
    (hM:∀z,|a z|≤M0)(hK:0≤K)(hβ:0≤β)(hβ1:β<1)
    (hh:∀z w,|a z-a w|≤K*|z-w|^β)(j:ℕ):
    let r:=CompactMollifier.radius (j+1)
    let L:=κ/(128*r^2)
    let tail:=GaussianCircleMass.decay (2-β) L (Real.sqrt ((b:ℝ)-(v:ℝ)))
    let ED:=(∫ω,‖S.second v ω-S.first v ω‖^2 ∂μ)
    let Cdisp:=2*((θ-η)^2+(Bnext:ℝ)*PastReferenceBracket.energyConstant P κ θ η 1)
    Integrable (fun ω=>‖(Y b hbH ρ hΛ1 hρ.le a j θ η) ω‖^2) μ ∧
      (∫ω,‖(Y b hbH ρ hΛ1 hρ.le a j θ η) ω‖^2 ∂μ)≤
        NativeGaussianBesselCost.bound (2-β) L Λ ρ tail*
          (NativeFrozenReferenceCovarianceKernel.prefactor K β j)^2*
            min 1 (Cdisp*ED/r^2):=by
  intro r L tail ED Cdisp
  have hb0:0<b:=bot_le.trans_lt hvb
  have he:=FirstGammaTerminalReferenceEnergy.energy
    (𝓕:=𝓕) (μ:=μ) (H:=H) (Λ:=Λ) (κ:=κ) (hκ:=hκ) (haU:=haU) (haV:=haV)
    (hell:=hell) (hbU:=hbU) (hbV:=hbV) (I₀:=I₀) (I₁:=I₁) (u₀:=u₀) (S:=S)
    (J:=J) (P:=P) (hκP:=hκP) (hΛ:=zero_le_one.trans hΛ1) (v:=v) (hH:=hH)
    (B:=B) (hBDG:=hBDG) (hIJ₀:=hIJ₀) (hIJ₁:=hIJ₁) (hsmall:=hsmall)
    (Bpast:=Bpast) (hBDGpast:=hBDGpast)
    b hvb hbH hwindow θ η hnull B0 B1 hBDG0 hBDG1 hlocal Bnext hBDGnext
  let D:=fun z:Ω×HeatCircle=>(Field b hbH θ) z-(Field b hbH η) z
  have hDi:Integrable (fun z=>D z^2) (μ.prod AddCircle.haarAddCircle):=he.1
  have hDE:(∫z,D z^2 ∂μ.prod AddCircle.haarAddCircle)≤Cdisp*ED:=he.2
  have hDm:Measurable D:=
    (NativeFrozenReferenceBandFields.field_measurable 𝓕 μ H b v P Λ κ hκ hκP
      OldU OldD OldUM OldDM hbH ((show (b:ℝ)≤(H:ℝ) by exact_mod_cast hbH).trans hH) I₀ I₁ hb0 hnull B0 B1 hBDG0 hBDG1 θ).sub
    (NativeFrozenReferenceBandFields.field_measurable 𝓕 μ H b v P Λ κ hκ hκP
      OldU OldD OldUM OldDM hbH ((show (b:ℝ)≤(H:ℝ) by exact_mod_cast hbH).trans hH) I₀ I₁ hb0 hnull B0 B1 hBDG0 hBDG1 η)
  have hp:0≤NativeFrozenReferenceCovarianceKernel.prefactor K β j:=by
    unfold NativeFrozenReferenceCovarianceKernel.prefactor
    exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hK)
      (GaussianHeatBandRootEnvelope.constant_nonneg β)) (Real.rpow_nonneg (CompactMollifier.radius_pos _).le _)
  have haE:=ClippedDisplacementEnergy.bound (μ.prod AddCircle.haarAddCircle) D hDm hDi
    (CompactMollifier.radius_pos (j+1)) hp
  have hScaledI:Integrable (fun z=>((Scaled b hbH K β j θ η) z)^2) (μ.prod AddCircle.haarAddCircle):=haE.1
  have hScaledE:(∫ω,∫x:HeatCircle,((Scaled b hbH K β j θ η) (ω,x))^2 ∂AddCircle.haarAddCircle ∂μ)≤
      (NativeFrozenReferenceCovarianceKernel.prefactor K β j)^2*min 1 (Cdisp*ED/r^2):=by
    rw [←integral_prod _ hScaledI]
    exact haE.2.trans (mul_le_mul_of_nonneg_left
      (min_le_min_left 1 (div_le_div_of_nonneg_right hDE (sq_nonneg r))) (sq_nonneg _))
  have hL:0<L:=by dsimp [L,r];positivity [CompactMollifier.radius_pos (j+1)]
  have htail:0≤tail:=GaussianCircleMass.decay_nonneg hL.le (Real.sqrt_nonneg _)
  have hcost:0≤NativeGaussianBesselCost.bound (2-β) L Λ ρ tail:=by
    unfold NativeGaussianBesselCost.bound
    have hm:0<NativeGaussianCircleMass.mass (2-β) L:=NativeGaussianBesselCost.mass_pos (by linarith) hL
    have hg:0<Real.Gamma ρ:=Real.Gamma_pos_of_pos hρ
    have hhalf:0<1/2-ρ:=by linarith
    exact add_nonneg
      (mul_nonneg (add_nonneg hm.le htail) (Real.rpow_nonneg (zero_le_one.trans hΛ1) _))
      (mul_nonneg (div_nonneg (add_nonneg (div_nonneg zero_le_one hρ.le)
        (div_nonneg zero_le_one hhalf.le)) hg.le)
        (Real.rpow_nonneg (mul_nonneg NativeGaussianBesselCost.heatFactor_pos.le hm.le) _))
  have hy:=NativeFrozenReferenceBesselEnergy.energy 𝓕 μ H b v P Λ κ hκ hκP
    OldU OldD OldUM OldDM hbH ((show (b:ℝ)≤(H:ℝ) by exact_mod_cast hbH).trans hH) I₀ I₁ J hIJ₀ hIJ₁ hvb hΛ1 ρ hρ hρhalf
    hsmallrow hsmalltime hnull B B0 B1 hBDG hBDG0 hBDG1 hJ hlocalJ
    θ η ha hM hK hβ hβ1 hh j
  refine ⟨hy.1,?_⟩
  exact hy.2.trans ((mul_le_mul_of_nonneg_left hScaledE hcost).trans_eq (by ring))
end SHE.FirstGammaTerminalReferenceBessel
