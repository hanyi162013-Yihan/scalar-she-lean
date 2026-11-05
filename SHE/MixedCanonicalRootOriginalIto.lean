module

public import SHE.MixedCanonicalRootFields
public import SHE.NativeScalarFourierWeight
public import SHE.NativeBesselFieldAE
public import SHE.ControlledReferenceFamilyResidual
public import SHE.PastParameterOriginalIto
public import SHE.PastItoLimitWitness
public import SHE.HistoryMeasureGeometry

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
set_option quotPrecheck false

namespace SHE.MixedCanonicalRootOriginalIto
open MeasureTheory Set PredictableL2 NativeHeatObservation NativeObservationNaturality
open FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation CutoffWordLevel
open GaussianTaylorAverage JointWordAnalytic
open GaussianItoTest
open scoped ENNReal NNReal
local instance : Fact (0<(1:ℝ)) := ⟨zero_lt_one⟩
local instance : Fact (0<2*Real.pi) := ⟨by positivity⟩
local instance : MeasurableSpace CircleHeat.CircleL2 := borel _
local instance : BorelSpace CircleHeat.CircleL2 := ⟨rfl⟩
local instance : MeasurableSpace CircleL2 := borel _
local instance : BorelSpace CircleL2 := ⟨rfl⟩
local instance mixedCanonicalRootOriginalIto_circleSecondCountable : SecondCountableTopology StoppedFourier.CircleL2 :=
  (_root_.fourierBasis (T:=2*Real.pi)).repr.toHomeomorph.secondCountableTopology
local instance : MeasurableSpace RealL2 := borel _
local instance : BorelSpace RealL2 := ⟨rfl⟩
local instance : MeasurableSpace RealHaarInput := borel _
local instance : BorelSpace RealHaarInput := ⟨rfl⟩
local instance : MeasurableSpace (Both RealHaarInput) := borel _
local instance : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
variable {Ω : Type} [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
variable (Λ κ : ℝ) (hκ : 0<κ) {aU aV : ℝ→ℝ} (haU : Measurable aU) (haV : Measurable aV) {ell M : ℝ}
variable (hell : 0<ell) (hbU : ∀ z,ell≤aU z ∧ aU z≤M) (hbV : ∀ z,ell≤aV z ∧ aV z≤M)
variable (I₀ I₁ : StandardTerminalIto (C := RealHaarIntegrand.Columns) (E := RealL2) 𝓕 μ H)
variable (u₀ v₀ : RealL2)
variable (S : MixedNativeAdditiveResidualPair.Solution 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀)

open ControlledProfile ControlledReferenceLevel
variable (P : CanonicalCovariance.ProfileParameters) (hAs : SmoothCylinders.BoundedSmooth (fun z => κ+aV z))
variable (θ : ℝ) (v b : ℝ≥0) (hvb : v≤b)
variable (Z : VariableObservations.Family HeatCircle 1)
variable (htarget : ∀ x i,(b:ℝ)≤(Z.observations x i).target)
variable (hstop : ∀ x i,(b:ℝ)≤(Z.observations x i).stop)
variable (F : HeatCircle→WordRecursion.State 1→ℝ) (hF : UniformSmooth.UniformBoundedSmooth F)
variable (hFm : Measurable (fun q : HeatCircle×WordRecursion.State 1 => F q.1 q.2))


local notation "dU" => MixedNativeJointHistory.firstData 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
local notation "dV" => MixedNativeJointHistory.secondData 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
local notation "U" => (dU).physicalState
local notation "V" => (dV).physicalState
local notation "XU" => (dU).physicalField
local notation "XV" => (dV).physicalField

variable (hsmall : ProfileStability.memoryConstant P.lower P.holder P.exponent*
  ProfileVolterra.powerConstant ((P.exponent-2)/4)*P.horizon^(P.exponent/4)≤1/2)

local notation "pastParameter" => MixedNativeRandomReferenceStep.randomParameter 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S v

open Filter Topology
local notation "Base" => ControlledReferenceFamilyLevel.level P (fun z => κ+aV z) hAs Λ θ v b hvb Z htarget hstop F hF hFm

open CutoffWordHistories
local notation "LS" => ControlledReferenceFamilySections.leafSection 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S P hAs θ v b hvb Z htarget hstop F hF hFm
local notation "RS" => ControlledReferenceFamilySections.referenceSection 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S P hAs θ v b hvb Z htarget hstop F hF hFm
local notation "MS" => ControlledReferenceFamilySections.markSection 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S P hAs θ v b hvb Z htarget hstop F hF hFm

local notation "K" => ControlledReferenceFamilyResidual.residual 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
  P hAs θ v b hvb Z htarget hstop F hF hFm
local notation "N" => (fun p:Inputs=>MixedUncutSampleExpansion.noiseMass 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S (Base p))

local notation "Field"=>MixedCanonicalRootFields.field
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
  P hAs θ v b hvb Z htarget hstop F hF hFm
local notation "D"=>MixedCanonicalRootFields.residual
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
  P hAs θ v b hvb Z htarget hstop F hF hFm

include hsmall in
theorem section_memLp (hΛ:0≤Λ)(depth:ℕ)(ω:Ω):
    MemLp (fun x:HeatCircle=>D depth (ω,x)) 2 AddCircle.haarAddCircle:=by
  have hp(i:Fin 3)(k:ℕ):MemLp (fun x:HeatCircle=>Field i k (ω,x)) 2 AddCircle.haarAddCircle:=by
    obtain ⟨C,hC,hCb⟩:=MixedCanonicalRootFields.field_bound
      𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
      P hAs θ v b hvb Z htarget hstop F hF hFm hsmall hΛ k
    exact MemLp.of_bound ((MixedCanonicalRootFields.field_measurable
      𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
      P hAs θ v b hvb Z htarget hstop F hF hFm hsmall hΛ i k).comp
        (measurable_const.prodMk measurable_id)).aestronglyMeasurable C (ae_of_all _ (fun x=>hCb i (ω,x)))
  exact (((hp 0 0).sub (memLp_finsetSum _ (fun k _=>hp 1 k))).sub
    (memLp_finsetSum _ (fun k _=>hp 2 k))).sub (hp 0 depth)

variable (J:StandardTerminalIto (C:=Both RealHaarInput) (E:=ℝ) 𝓕 μ H)
variable (hIJ₀:StandardScalarNaturality I₀ (leftIntegral 𝓕 μ H J))
variable (hIJ₁:StandardScalarNaturality I₁ (rightIntegral 𝓕 μ H J))
variable (hrootStop:∀x,(Z.observations x 0).stop=(b:ℝ))
variable (hrootTarget:∀x,(Z.observations x 0).target=(b:ℝ))
variable (hcenter:∀x,(Z.observations x 0).center=x)
variable (hnull:NullCompleteFiltration.ContainsNullSets 𝓕 μ)
variable (hJ:StandardFiniteIto.Universal 𝓕 μ H J) (hlocal:StandardTerminalPastLocality J)
variable (hΛ:0≤Λ) (hbH:b≤H) (hvb':v<b)

include hsmall hIJ₀ hIJ₁ hrootStop hrootTarget hcenter hnull hJ hlocal hΛ hbH hvb' in
/-- The literal actual random-reference spatial residual, tested against
a nonnegative bounded root density, is the SAME original scalar Ito
integral after zero-root-gap and both recursive-cutoff limits. -/
theorem original_input_density
    (g:HeatCircle→ℝ)(hg:Measurable g)(B:ℝ≥0)
    (hg0:∀x,0≤g x)(hgB:∀x,g x≤B)(depth:ℕ):
    ∃input:Process (E:=Both RealHaarInput) 𝓕 μ H,J.integral input=ᵐ[μ]
      fun ω=>∫x:HeatCircle,g x*D depth (ω,x) ∂AddCircle.haarAddCircle:=by
  let ν:Measure HeatCircle:=AddCircle.haarAddCircle.withDensity (fun x=>ENNReal.ofReal (g x))
  have hν:ν≤(B:ℝ≥0∞) • (AddCircle.haarAddCircle:Measure HeatCircle):=by
    calc
      _≤AddCircle.haarAddCircle.withDensity (fun _:HeatCircle=>(B:ℝ≥0∞)):=
        withDensity_mono (ae_of_all _ (fun x=>by
          simpa only [ENNReal.ofReal_coe_nnreal] using ENNReal.ofReal_le_ofReal (hgB x)))
      _=_:=withDensity_const _
  haveI:IsFiniteMeasure ((B:ℝ≥0∞) • (AddCircle.haarAddCircle:Measure HeatCircle)):=
    (AddCircle.haarAddCircle:Measure HeatCircle).smul_finite ENNReal.coe_ne_top
  haveI:IsFiniteMeasure ν:=isFiniteMeasure_of_le ((B:ℝ≥0∞) • (AddCircle.haarAddCircle:Measure HeatCircle)) hν
  obtain ⟨input,hi⟩:=MixedCanonicalUncutOriginalNoise.random_residual_original_input
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
    P hAs θ v b hvb Z htarget hstop F hF hFm hsmall J hIJ₀ hIJ₁ hrootStop hrootTarget hcenter
    hnull hJ hlocal hΛ hbH hvb' ν B hν depth
  refine ⟨input,hi.trans ?_⟩
  filter_upwards with ω
  rw [←MixedCanonicalRootFields.residual_integral
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
    P hAs θ v b hvb Z htarget hstop F hF hFm hsmall hΛ ν depth ω]
  rw [show ν=AddCircle.haarAddCircle.withDensity (fun x=>ENNReal.ofReal (g x)) from rfl,
    integral_withDensity_eq_integral_toReal_smul hg.ennreal_ofReal
      (ae_of_all _ (fun _=>ENNReal.ofReal_lt_top))]
  apply integral_congr_ae
  filter_upwards with x
  simp only [ENNReal.toReal_ofReal (hg0 x),smul_eq_mul]

include hsmall hIJ₀ hIJ₁ hrootStop hrootTarget hcenter hnull hJ hlocal hΛ hbH hvb' in
/-- Every bounded signed spatial root test of the genuine whole random
finite stochastic residual remains an integral of the original J. -/
theorem original_input_weighted
    (g:HeatCircle→ℝ)(hg:Measurable g)(B:ℝ≥0)(hgB:∀x,‖g x‖≤B)(depth:ℕ):
    ∃input:Process (E:=Both RealHaarInput) 𝓕 μ H,J.integral input=ᵐ[μ]
      fun ω=>∫x:HeatCircle,g x*D depth (ω,x) ∂AddCircle.haarAddCircle:=by
  let gp:=fun x:HeatCircle=>max (g x) 0
  let gn:=fun x:HeatCircle=>max (-g x) 0
  have hgp:Measurable gp:=hg.max measurable_const
  have hgn:Measurable gn:=hg.neg.max measurable_const
  have hgpB(x:HeatCircle):gp x≤B:=max_le ((le_abs_self _).trans (hgB x)) B.2
  have hgnB(x:HeatCircle):gn x≤B:=max_le ((neg_le_abs _).trans (hgB x)) B.2
  obtain ⟨ip,hip⟩:=original_input_density
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
    P hAs θ v b hvb Z htarget hstop F hF hFm hsmall J hIJ₀ hIJ₁ hrootStop hrootTarget hcenter
    hnull hJ hlocal hΛ hbH hvb' gp hgp B (fun x=>le_max_right _ _) hgpB depth
  obtain ⟨ineg,hin⟩:=original_input_density
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
    P hAs θ v b hvb Z htarget hstop F hF hFm hsmall J hIJ₀ hIJ₁ hrootStop hrootTarget hcenter
    hnull hJ hlocal hΛ hbH hvb' gn hgn B (fun x=>le_max_right _ _) hgnB depth
  refine ⟨ip-ineg,?_⟩
  have hs:J.integral (ip-ineg)=J.integral ip-J.integral ineg:=map_sub J.integral ip ineg
  have ha:=Lp.coeFn_sub (J.integral ip) (J.integral ineg)
  rw [←hs] at ha
  filter_upwards [hip,hin,ha] with ω hp hn hhω
  rw [hhω,Pi.sub_apply,hp,hn]
  have hiY:Integrable (fun x:HeatCircle=>D depth (ω,x)) AddCircle.haarAddCircle:=
    (section_memLp 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
      P hAs θ v b hvb Z htarget hstop F hF hFm hsmall hΛ depth ω).integrable (by norm_num)
  have hipY:=hiY.bdd_mul (c:=(B:ℝ)) hgp.aestronglyMeasurable (ae_of_all _ (fun x=>by
    rw [Real.norm_eq_abs,abs_of_nonneg (le_max_right _ _)]
    exact hgpB x))
  have hinY:=hiY.bdd_mul (c:=(B:ℝ)) hgn.aestronglyMeasurable (ae_of_all _ (fun x=>by
    rw [Real.norm_eq_abs,abs_of_nonneg (le_max_right _ _)]
    exact hgnB x))
  rw [←integral_sub hipY hinY]
  apply integral_congr_ae
  filter_upwards with x
  change gp x*D depth (ω,x)-gn x*D depth (ω,x)=g x*D depth (ω,x)
  rw [←sub_mul]
  congr 1
  dsimp only [gp,gn]
  by_cases hx:0≤g x
  · rw [max_eq_left hx,max_eq_right (neg_nonpos.mpr hx)];ring
  · have hx':g x≤0:=le_of_not_ge hx
    rw [max_eq_right hx',max_eq_left (neg_nonneg.mpr hx')];ring

include hsmall hIJ₀ hIJ₁ hrootStop hrootTarget hcenter hnull hJ hlocal hΛ hbH hvb' in
theorem original_input_fourier (w:ℝ)(a:ℂ→L[ℝ]ℝ)(l:ℤ)(depth:ℕ):
    ∃input:Process (E:=Both RealHaarInput) 𝓕 μ H,J.integral input=ᵐ[μ]
      fun ω=>w*a (fourierCoeff (fun x:HeatCircle=>(D depth (ω,x):ℂ)) l):=by
  obtain ⟨input,hi⟩:=original_input_weighted
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
    P hAs θ v b hvb Z htarget hstop F hF hFm hsmall J hIJ₀ hIJ₁ hrootStop hrootTarget hcenter
    hnull hJ hlocal hΛ hbH hvb'
    (NativeScalarFourierWeight.value w a l) (NativeScalarFourierWeight.measurable w a l)
    ⟨‖w‖*‖a‖,mul_nonneg (norm_nonneg _) (norm_nonneg _)⟩
    (NativeScalarFourierWeight.bound w a l) depth
  refine ⟨input,hi.trans (ae_of_all _ (fun ω=>?_))⟩
  exact NativeScalarFourierWeight.integral _
    ((section_memLp 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
      P hAs θ v b hvb Z htarget hstop F hF hFm hsmall hΛ depth ω).integrable (by norm_num)) w a l


/-- The genuine native Bessel-smoothed whole finite stochastic residual,
with its actual random-reference root retained. -/
def value (hL:1≤Λ){ρ:ℝ}(hρ:0≤ρ)(depth:ℕ)(ω:Ω):CircleL2:=
  NativeBesselFieldAE.value Λ ρ hL hρ (fun z:Ω×HeatCircle=>(D depth z:ℂ)) ω
local notation "Value"=>value 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
  P hAs θ v b hvb Z htarget hstop F hF hFm

include hsmall in
theorem value_measurable (hL:1≤Λ){ρ:ℝ}(hρ:0≤ρ)(depth:ℕ):Measurable (Value hL hρ depth):=
  NativeBesselFieldAE.measurable Λ ρ hL hρ _ (Complex.continuous_ofReal.measurable.comp
    (MixedCanonicalRootFields.residual_measurable
      𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
      P hAs θ v b hvb Z htarget hstop F hF hFm hsmall (zero_le_one.trans hL) depth))

include hsmall hIJ₀ hIJ₁ hrootStop hrootTarget hcenter hnull hJ hlocal hbH hvb' in
/-- ALL real and imaginary Fourier coordinates of the actual random
reference finite Hilbert noise are SAME-original-J integrals on ONE
sample event. No parameterwise exceptional set is sampled randomly. -/
theorem hilbert_noise_coefficients (hL:1≤Λ){ρ:ℝ}(hρ:0≤ρ)(depth:ℕ):
    ∃inputR inputI:ℤ→Process (E:=Both RealHaarInput) 𝓕 μ H,∀ᵐω∂μ,∀l:ℤ,
      J.integral (inputR l) ω=(fourierCoeff (Value hL hρ depth ω) l).re ∧
      J.integral (inputI l) ω=(fourierCoeff (Value hL hρ depth ω) l).im:=by
  let w:=fun l:ℤ=>(Λ+(l:ℝ)^2)^(-ρ/2)
  have hexR(l:ℤ):∃input:Process (E:=Both RealHaarInput) 𝓕 μ H,J.integral input=ᵐ[μ]
      fun ω=>w l*Complex.re (fourierCoeff (fun x:HeatCircle=>(D depth (ω,x):ℂ)) l):=
    original_input_fourier
      𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
      P hAs θ v b hvb Z htarget hstop F hF hFm hsmall J hIJ₀ hIJ₁ hrootStop hrootTarget hcenter
      hnull hJ hlocal (zero_le_one.trans hL) hbH hvb' (w l) Complex.reCLM l depth
  have hexI(l:ℤ):∃input:Process (E:=Both RealHaarInput) 𝓕 μ H,J.integral input=ᵐ[μ]
      fun ω=>w l*Complex.im (fourierCoeff (fun x:HeatCircle=>(D depth (ω,x):ℂ)) l):=
    original_input_fourier
      𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
      P hAs θ v b hvb Z htarget hstop F hF hFm hsmall J hIJ₀ hIJ₁ hrootStop hrootTarget hcenter
      hnull hJ hlocal (zero_le_one.trans hL) hbH hvb' (w l) Complex.imCLM l depth
  choose inputR hR using hexR
  choose inputI hI using hexI
  refine ⟨inputR,inputI,?_⟩
  let E:=fun z:Ω×HeatCircle=>(D depth z:ℂ)
  have hE:Measurable E:=Complex.continuous_ofReal.measurable.comp
    (MixedCanonicalRootFields.residual_measurable
      𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
      P hAs θ v b hvb Z htarget hstop F hF hFm hsmall (zero_le_one.trans hL) depth)
  have hp(ω:Ω):MeasurableL2FieldAE.squareMass AddCircle.haarAddCircle E ω<∞:=
    (MeasurableL2FieldAE.section_memLp_iff AddCircle.haarAddCircle E hE ω).mp
      (section_memLp 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
        P hAs θ v b hvb Z htarget hstop F hF hFm hsmall (zero_le_one.trans hL) depth ω).ofReal
  filter_upwards [ae_all_iff.mpr hR,ae_all_iff.mpr hI] with ω hr hi l
  have hc:=NativeBesselFieldAE.coefficients Λ ρ hL hρ E hE ω (hp ω) l
  change fourierCoeff (Value hL hρ depth ω) l=(w l:ℂ)*fourierCoeff (fun x=>E (ω,x)) l at hc
  constructor
  · rw [hc,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
    exact hr l
  · rw [hc,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,zero_mul,add_zero]
    exact hi l

end SHE.MixedCanonicalRootOriginalIto
