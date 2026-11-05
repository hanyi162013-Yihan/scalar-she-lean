module
public import SHE.MixedPastDerivativeRMS
public import SHE.MeanThetaAverage
public import SHE.FiniteGaussianAveraging
public import SHE.SectionFirstMoment
public import SHE.RelativeAgeSections

public import SHE.MixedPastProfileEnergy
public import SHE.MixedPastProfileDerivative
public import SHE.ScalarFibreRMS
public import SHE.ForestLeafL2
public import SHE.MixedCurrentInputMoments
public import SHE.MixedPastJointData
public import SHE.MixedNativePastProfileCentering
public import SHE.ControlledProfile
public import SHE.PastHybridIntegral
public import SHE.PastItoAlgebra
public import SHE.MixedNativePairObservation
public import SHE.NativePairScaledMartingale
public import SHE.NativePairLocalMartingale
public import SHE.NativePairExtendedMartingale

@[expose] public section
noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000

namespace SHE.MixedPastBaselineThetaRMS
open MeasureTheory PredictableL2 NativeHeatObservation NativeObservationNaturality
open FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation StoppedItoInputs
open scoped NNReal ENNReal
local instance mixedPastDerivativeRMS_periodPositive : Fact (0<2*Real.pi) := ⟨by positivity⟩
local instance mixedPastDerivativeRMS_realSigma : MeasurableSpace RealL2 := borel _
local instance mixedPastDerivativeRMS_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance mixedPastDerivativeRMS_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance mixedPastDerivativeRMS_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance mixedPastDerivativeRMS_blockSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance mixedPastDerivativeRMS_blockBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
variable {Ω : Type*} [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
variable (Λ κ : ℝ) (hκ : 0<κ) {aU aV : ℝ→ℝ} (haU : Measurable aU) (haV : Measurable aV) {ell M : ℝ}
variable (hell : 0<ell) (hbU : ∀ z,ell≤aU z ∧ aU z≤M) (hbV : ∀ z,ell≤aV z ∧ aV z≤M)
variable (I₀ I₁ : StandardTerminalIto (C := RealHaarIntegrand.Columns) (E := RealL2) 𝓕 μ H)
variable (u₀ v₀ : RealL2)
variable (S : MixedNativeAdditiveResidualPair.Solution 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀)
variable (J : StandardTerminalIto (C := Both RealHaarInput) (E := ℝ) 𝓕 μ H)
variable (hIJ₀ : StandardScalarNaturality I₀ (leftIntegral 𝓕 μ H J))
variable (hIJ₁ : StandardScalarNaturality I₁ (rightIntegral 𝓕 μ H J))

local instance mixedPastDerivativeRMS_circleSigma : MeasurableSpace CircleL2 := borel _
local instance mixedPastDerivativeRMS_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩

open ControlledProfile

open AddCircle Set Real
local instance : Fact (0<2*Real.pi):=⟨by positivity⟩

attribute [local irreducible] MixedPastDerivativeRMS.field MixedPastJointData.pastU MixedPastJointData.pastD

local notation "Field"=>MixedPastDerivativeRMS.field 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S

def amplitude (P:CanonicalCovariance.ProfileParameters)(v:ℝ≥0)(r:ℝ)(x:HeatCircle):ℝ:=
  ∫θ,Real.sqrt (∫ω,|Field P v r θ (ω,x)|^2 ∂μ) ∂MeanThetaAverage.thetaMeasure

include hIJ₀ hIJ₁ in
/-- Theta averages the genuine sample RMS before the spatial square.
A measurable energy predicate justifies theta/age AE interchange, so
this can subsequently be pulled back to every original old leaf age. -/
theorem age_energy (P:CanonicalCovariance.ProfileParameters)(hΛ:0≤Λ)
    (hsmallPoint:ProfileStability.memoryConstant P.lower P.holder P.exponent*
      ProfileVolterra.powerConstant ((P.exponent-2)/4)*P.horizon^(P.exponent/4)≤1/2)
    (hsmallL2:ProfileStability.memoryConstant P.lower P.holder P.exponent*
      ProfileVolterra.powerConstant ((P.exponent-1)/4)*P.horizon^(P.exponent/4)≤1/2)
    (hinit:v₀=u₀)(v:ℝ≥0)(hvH:v≤H)(hv1:(v:ℝ)≤1)
    (p:ℕ)(hp:0<p)(B:ℝ≥0)(hBDG:StandardTerminalBDGPower p J B):
    ∀ᵐr∂volume.restrict (Set.Ici (0:ℝ)),
      let A:=amplitude 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S P v r
      Integrable (fun x=>A x^2) haarAddCircle ∧
        (∫x,A x^2 ∂haarAddCircle)≤(ControlledProfile.sharpUnit P*r^((P.exponent-1)/4))^2*
          (∫ω,‖S.second v ω-S.first v ω‖^2 ∂μ):=by
  let τ:=MeanThetaAverage.thetaMeasure
  let η:Measure (Ω×HeatCircle):=μ.prod haarAddCircle
  let raw:(ℝ×ℝ)×(Ω×HeatCircle)→ℝ:=fun z=>Field P v z.1.2 z.1.1 z.2
  have hu:=(MixedPastJointData.pastU_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S v).mono (𝓕.le v) le_rfl
  have hd:=(MixedPastJointData.pastD_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S v).mono (𝓕.le v) le_rfl
  have hraw:Measurable raw:=by
    have hh:=ControlledProfile.random_derivative_measurable P hΛ _ _ hu hd hsmallPoint
    have hm:Measurable (fun z:(ℝ×ℝ)×(Ω×HeatCircle)=>((z.2.1,(z.1.2,z.2.2)),z.1.1)):=
      (measurable_snd.fst.prodMk (measurable_fst.snd.prodMk measurable_snd.snd)).prodMk measurable_fst.fst
    convert! hh.comp hm using 1
    funext z
    simp only [raw,MixedPastDerivativeRMS.field,MixedPastJointData.pastU,MixedPastJointData.pastD,Function.comp_apply]
  let budget:ℝ→ℝ:=fun r=>(ControlledProfile.sharpUnit P*r^((P.exponent-1)/4))^2*
    (∫ω,‖S.second v ω-S.first v ω‖^2 ∂μ)
  have hb:Measurable budget:=by fun_prop
  have hsq:Measurable (fun z=>|raw z|^2):=(continuous_abs.measurable.comp hraw).pow_const 2
  have hP:MeasurableSet {z:ℝ×ℝ|Integrable (fun y=>|raw (z,y)|^2) η ∧
      (∫y,|raw (z,y)|^2 ∂η)≤budget z.2}:=
    (measurableSet_integrable hsq.stronglyMeasurable).inter
      (measurableSet_le hsq.stronglyMeasurable.integral_prod_right'.measurable (hb.comp measurable_snd))
  have hs0:∀ᵐθ∂τ,∀ᵐr∂volume.restrict (Set.Ici (0:ℝ)),
      Integrable (fun y=>|raw ((θ,r),y)|^2) η ∧
        (∫y,|raw ((θ,r),y)|^2 ∂η)≤budget r:=by
    have hh:=MixedPastProfileEnergy.derivative_spatial_energy
      𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S J hIJ₀ hIJ₁
      P hΛ hsmallPoint hsmallL2 hinit v hvH hv1 p hp B hBDG
    have hh':=ae_restrict_of_ae (s:=Set.Ioc (0:ℝ) 1) hh
    convert! hh' using 1 <;> simp only [raw,η,budget,MixedPastDerivativeRMS.field]
  have hs:∀ᵐr∂volume.restrict (Set.Ici (0:ℝ)),∀ᵐθ∂τ,
      Integrable (fun y=>|raw ((θ,r),y)|^2) η ∧
        (∫y,|raw ((θ,r),y)|^2 ∂η)≤budget r:= (Measure.ae_ae_comm hP).mp hs0
  filter_upwards [hs] with r hr
  intro A
  let G:ℝ×HeatCircle→ℝ:=fun z=>Real.sqrt (∫ω,|raw ((z.1,r),(ω,z.2))|^2 ∂μ)
  have hm:Measurable (fun z:Ω×(ℝ×HeatCircle)=>raw ((z.2.1,r),(z.1,z.2.2))):=
    hraw.comp ((measurable_snd.fst.prodMk measurable_const).prodMk
      (measurable_fst.prodMk measurable_snd.snd))
  have hG:Measurable G:=ScalarFibreRMS.measurable μ _ hm
  have hsec:∀ᵐθ∂τ,Integrable (fun x=>G (θ,x)^2) haarAddCircle ∧
      (∫x,G (θ,x)^2 ∂haarAddCircle)≤budget r:=by
    filter_upwards [hr] with θ hθ
    have hmf:Measurable (fun z:Ω×HeatCircle=>raw ((θ,r),z)):=
      hraw.comp (measurable_const.prodMk measurable_id)
    have he:=ScalarFibreRMS.memLp_energy μ haarAddCircle _ hmf hθ.1
    refine ⟨(memLp_two_iff_integrable_sq he.1.aestronglyMeasurable).mp he.1,?_⟩
    have heq:=he.2
    rw [ProfileL2.normTwo_sq] at heq
    exact heq.le.trans hθ.2
  have hjs:=SectionFirstMoment.joint_integrable haarAddCircle τ
    (fun z:HeatCircle×ℝ=>G (z.2,z.1)^2) ((hG.comp measurable_swap).pow_const 2)
    (fun _=>budget r) (integrable_const _) (hsec.mono (fun θ hθ=>⟨hθ.1,by
      have heq:(fun x:HeatCircle=>|G (θ,x)^2|)=(fun x=>G (θ,x)^2):=
        funext (fun x=>abs_of_nonneg (sq_nonneg (G (θ,x))))
      rw [heq]
      exact hθ.2⟩))
  have hj:Integrable (fun z:ℝ×HeatCircle=>G z^2) (τ.prod haarAddCircle):=hjs.1.swap
  have ha:=FiniteGaussianAveraging.square_average_le τ haarAddCircle G hG hj
  refine ⟨ha.1,ha.2.trans ?_⟩
  simp only [probReal_univ,one_mul]
  rw [integral_prod _ hj]
  have hh:=integral_mono_ae hj.integral_prod_left (integrable_const (budget r)) (hsec.mono (fun _ h=>h.2))
  simpa only [integral_const,probReal_univ,smul_eq_mul,one_mul] using hh

end SHE.MixedPastBaselineThetaRMS
