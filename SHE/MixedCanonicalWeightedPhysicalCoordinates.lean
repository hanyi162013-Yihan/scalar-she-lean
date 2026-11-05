module

public import SHE.MixedCanonicalUncutPhysicalInput
public import SHE.RootDensityHistory
public import SHE.MixedCanonicalPhysicalCoordinates
public import SHE.NativeScalarFourierWeight
public import SHE.MixedUncutPhysicalColumns
public import SHE.ScalarRootUncutPhysicalInput
public import SHE.MixedCanonicalPhysicalSections
public import SHE.PastParameterRawLimit
public import SHE.MixedCanonicalUncutOriginalNoise
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

namespace SHE.MixedCanonicalWeightedPhysicalCoordinates
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
local instance mixedCanonicalPhysicalCoordinates_circleSecondCountable : SecondCountableTopology StoppedFourier.CircleL2 :=
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

local notation "R₀"=>referenceData P (fun z=>κ+aV z) hAs Λ θ v b hvb (0,0)
local notation "Raw"=>(fun k p=>MixedUncutPhysicalGradient.raw
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S (Base p) k)

variable (J:StandardTerminalIto (C:=Both RealHaarInput) (E:=ℝ) 𝓕 μ H)
variable (hIJ₀:StandardScalarNaturality I₀ (leftIntegral 𝓕 μ H J))
variable (hIJ₁:StandardScalarNaturality I₁ (rightIntegral 𝓕 μ H J))
variable (hrootStop:∀x,(Z.observations x 0).stop=(b:ℝ))
variable (hrootTarget:∀x,(Z.observations x 0).target=(b:ℝ))
variable (hcenter:∀x,(Z.observations x 0).center=x)


def noise (k:ℕ)(z:Ω×History HeatCircle k):ℝ:=
  MixedUncutNoiseL2.value 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
    (Base (pastParameter z.1)) k z.2 z.1

def coordinate (k:ℕ)(ℓ:Both RealHaarInput→L[ℝ]ℝ)(z:(ℝ≥0×Ω)×History HeatCircle k):ℝ:=
  MixedUncutPhysicalColumns.coordinate 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
    (Base (pastParameter z.1.2)) k ℓ (z.2,z.1)
local notation "Noise"=>noise 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
  P hAs θ v b hvb Z htarget hstop F hF hFm
local notation "Coord"=>coordinate 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
  P hAs θ v b hvb Z htarget hstop F hF hFm

theorem noise_integrable (hΛ:0≤Λ)(ν:Measure HeatCircle)[IsFiniteMeasure ν](k:ℕ)(ω:Ω):
    Integrable (fun h=>Noise k (ω,h)) (historyMeasure R₀ ν k):=by
  let L:=Base (pastParameter ω)
  have he:historyMeasure (referenceData P (fun z=>κ+aV z) hAs Λ θ v b hvb (pastParameter ω)) ν k=
      historyMeasure R₀ ν k:=HistoryMeasureGeometry.historyMeasure_eq
        (R:=referenceData P (fun z=>κ+aV z) hAs Λ θ v b hvb (pastParameter ω)) (Q:=R₀) rfl rfl ν k
  have hi:=UncutHistoryMass.weight_integrable L ν k
  rw [he] at hi
  obtain ⟨C,hC,hCb⟩:=MixedUncutNoiseL2.bound
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S L hΛ k
  have hm:Measurable (fun h=>Noise k (ω,h)):=
    (MixedUncutNoiseL2.value_measurable
      𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S L k).comp
        (measurable_id.prodMk measurable_const)
  exact (hi.const_mul C).mono' hm.aestronglyMeasurable (ae_of_all _ (fun h=>hCb h ω))

theorem raw_measurable (k:ℕ)(p:Inputs):Measurable (Raw k p):=by
  have hh:=MixedUncutPhysicalGradient.raw_predictable
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S (Base p) k
  have hm:@Measurable (History HeatCircle k×(ℝ≥0×Ω)) (History HeatCircle k×(ℝ≥0×Ω)) inferInstance
      ((inferInstance:MeasurableSpace (History HeatCircle k)).prod 𝓕.predictable) id:=
    measurable_fst.prodMk (measurable_snd.mono le_rfl (predictable_le_product 𝓕))
  exact hh.comp hm

/-- One current/sample event gives integrability of EVERY raw linear
coordinate in the original history measure, before root weighting. -/
theorem coordinates_integrable (hΛ:0≤Λ)(hbH:b≤H)(hb1:(b:ℝ)≤1)
    (ν:Measure HeatCircle)[IsFiniteMeasure ν](k:ℕ):
    ∀ᵐz∂energyMeasure μ H,∀ℓ:Both RealHaarInput→L[ℝ]ℝ,
      Integrable (fun h=>Coord k ℓ (z,h)) (historyMeasure R₀ ν k):=by
  letI:IsFiniteMeasure (energyMeasure μ H):=by dsimp only [energyMeasure];infer_instance
  obtain ⟨B,hBi,hB⟩:=MixedCanonicalPhysicalSections.uniform_integrable_bound
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
    P hAs θ v b hvb Z htarget hstop F hF hFm k hΛ hbH hb1 ν
  filter_upwards [hBi.prod_left_ae] with z hzi ℓ
  have hr:Integrable (fun h=>Raw k (pastParameter z.2) (h,z)) (historyMeasure R₀ ν k):=
    hzi.mono' ((raw_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
      P hAs θ v b hvb Z htarget hstop F hF hFm k (pastParameter z.2)).comp
        (measurable_id.prodMk measurable_const)).aestronglyMeasurable
      (ae_of_all _ (fun h=>hB (pastParameter z.2) (h,z)))
  have hl:Integrable (fun h=>ℓ (Raw k (pastParameter z.2) (h,z))) (historyMeasure R₀ ν k):=
    ℓ.integrable_comp hr
  apply hl.congr
  filter_upwards with h
  exact MixedUncutPhysicalColumns.coordinate_eq
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
    (Base (pastParameter z.2)) k ℓ (h,z)

include hsmall hIJ₀ hIJ₁ hrootStop hrootTarget hcenter in
/-- A positive bounded root test keeps the original Ito output and the
literal retained-root raw coordinates on ONE current/sample event. -/
theorem original_input_density (hnull:NullCompleteFiltration.ContainsNullSets 𝓕 μ)
    (hJ:StandardFiniteIto.Universal 𝓕 μ H J)(hlocal:StandardTerminalPastLocality J)
    (hΛ:0≤Λ)(hbH:b≤H)(hb1:(b:ℝ)≤1)(hvb':v<b)
    (g:HeatCircle→ℝ)(hg:Measurable g)(B:ℝ≥0)(hg0:∀x,0≤g x)(hgB:∀x,g x≤B)(k:ℕ):
    ∃input:Process (E:=Both RealHaarInput) 𝓕 μ H,
      J.integral input=ᵐ[μ] (fun ω=>∫x:HeatCircle,g x*RootSectionAverage.average R₀ k (Noise k) (ω,x) ∂AddCircle.haarAddCircle) ∧
      (∀ω,Integrable (fun x:HeatCircle=>g x*RootSectionAverage.average R₀ k (Noise k) (ω,x)) AddCircle.haarAddCircle) ∧
      ∀ᵐz∂energyMeasure μ H,∀ℓ:Both RealHaarInput→L[ℝ]ℝ,
        Integrable (fun x:HeatCircle=>g x*RootSectionAverage.average R₀ k (Coord k ℓ) (z,x)) AddCircle.haarAddCircle ∧
        ℓ (input z)=∫x:HeatCircle,g x*RootSectionAverage.average R₀ k (Coord k ℓ) (z,x) ∂AddCircle.haarAddCircle:=by
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
  obtain ⟨input,hout,hraw⟩:=MixedCanonicalPhysicalCoordinates.original_input
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
    P hAs θ v b hvb Z htarget hstop F hF hFm hsmall J hIJ₀ hIJ₁
    hrootStop hrootTarget hcenter hnull hJ hlocal hΛ hbH hb1 hvb' ν B hν k
  have hNi(ω:Ω):Integrable (fun h=>Noise k (ω,h)) (historyMeasure R₀ ν k):=
    noise_integrable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
      P hAs θ v b hvb Z htarget hstop F hF hFm hΛ ν k ω
  refine ⟨input,hout.trans (ae_of_all _ (fun ω=>?_)),?_,?_⟩
  · exact RootDensityHistory.integral R₀ k g hg hg0 (Noise k) ω (hNi ω)
  · exact fun ω=>RootDensityHistory.integrable R₀ k g hg hg0 (Noise k) ω (hNi ω)
  · have hci:=coordinates_integrable
      𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
      P hAs θ v b hvb Z htarget hstop F hF hFm hΛ hbH hb1 ν k
    filter_upwards [hraw,hci] with z hz hzi ℓ
    refine ⟨RootDensityHistory.integrable R₀ k g hg hg0 (Coord k ℓ) z (hzi ℓ),?_⟩
    exact (hz ℓ).trans (RootDensityHistory.integral R₀ k g hg hg0 (Coord k ℓ) z (hzi ℓ))

include hsmall hIJ₀ hIJ₁ hrootStop hrootTarget hcenter in
/-- Every bounded signed root test preserves the SAME original Ito
output and all raw coordinates on one event. -/
theorem original_input_weighted (hnull:NullCompleteFiltration.ContainsNullSets 𝓕 μ)
    (hJ:StandardFiniteIto.Universal 𝓕 μ H J)(hlocal:StandardTerminalPastLocality J)
    (hΛ:0≤Λ)(hbH:b≤H)(hb1:(b:ℝ)≤1)(hvb':v<b)
    (g:HeatCircle→ℝ)(hg:Measurable g)(B:ℝ≥0)(hgB:∀x,‖g x‖≤B)(k:ℕ):
    ∃input:Process (E:=Both RealHaarInput) 𝓕 μ H,
      J.integral input=ᵐ[μ] (fun ω=>∫x:HeatCircle,g x*RootSectionAverage.average R₀ k (Noise k) (ω,x) ∂AddCircle.haarAddCircle) ∧
      ∀ᵐz∂energyMeasure μ H,∀ℓ:Both RealHaarInput→L[ℝ]ℝ,
        ℓ (input z)=∫x:HeatCircle,g x*RootSectionAverage.average R₀ k (Coord k ℓ) (z,x) ∂AddCircle.haarAddCircle:=by
  let gp:=fun x:HeatCircle=>max (g x) 0
  let gn:=fun x:HeatCircle=>max (-g x) 0
  have hgp:Measurable gp:=hg.max measurable_const
  have hgn:Measurable gn:=hg.neg.max measurable_const
  have hgpB(x:HeatCircle):gp x≤B:=max_le ((le_abs_self _).trans (hgB x)) B.2
  have hgnB(x:HeatCircle):gn x≤B:=max_le ((neg_le_abs _).trans (hgB x)) B.2
  have hdiff(x:HeatCircle):gp x-gn x=g x:=by
    dsimp only [gp,gn]
    by_cases hx:0≤g x
    · rw [max_eq_left hx,max_eq_right (neg_nonpos.mpr hx)];ring
    · have hx':g x≤0:=le_of_not_ge hx
      rw [max_eq_right hx',max_eq_left (neg_nonneg.mpr hx')];ring
  obtain ⟨ip,hip,hipI,hcp⟩:=original_input_density
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
    P hAs θ v b hvb Z htarget hstop F hF hFm hsmall J hIJ₀ hIJ₁ hrootStop hrootTarget hcenter
    hnull hJ hlocal hΛ hbH hb1 hvb' gp hgp B (fun _=>le_max_right _ _) hgpB k
  obtain ⟨ineg,hin,hinI,hcn⟩:=original_input_density
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
    P hAs θ v b hvb Z htarget hstop F hF hFm hsmall J hIJ₀ hIJ₁ hrootStop hrootTarget hcenter
    hnull hJ hlocal hΛ hbH hb1 hvb' gn hgn B (fun _=>le_max_right _ _) hgnB k
  have hmass(f:HeatCircle→ℝ)(hp:Integrable (fun x=>gp x*f x) AddCircle.haarAddCircle)
      (hn:Integrable (fun x=>gn x*f x) AddCircle.haarAddCircle):
      (∫x,gp x*f x ∂AddCircle.haarAddCircle)-(∫x,gn x*f x ∂AddCircle.haarAddCircle)=
        ∫x,g x*f x ∂AddCircle.haarAddCircle:=by
    rw [←integral_sub hp hn]
    apply integral_congr_ae
    filter_upwards with x
    rw [←sub_mul,hdiff]
  refine ⟨ip-ineg,?_,?_⟩
  · have ha:=Lp.coeFn_sub (J.integral ip) (J.integral ineg)
    rw [←map_sub] at ha
    filter_upwards [hip,hin,ha] with ω hp hn hh
    rw [hh,Pi.sub_apply,hp,hn]
    exact hmass _ (hipI ω) (hinI ω)
  · have ha:=ae_eq_of_ae_eq_trim (Lp.coeFn_sub ip ineg)
    filter_upwards [hcp,hcn,ha] with z hp hn hz ℓ
    rw [hz]
    change ℓ (ip z-ineg z)=_
    rw [map_sub,(hp ℓ).2,(hn ℓ).2]
    exact hmass _ (hp ℓ).1 (hn ℓ).1

include hsmall hIJ₀ hIJ₁ hrootStop hrootTarget hcenter in
/-- Actual Fourier tests retain the SAME input's full raw-coordinate
identity, rather than merely an output-only Ito witness. -/
theorem original_input_fourier (hnull:NullCompleteFiltration.ContainsNullSets 𝓕 μ)
    (hJ:StandardFiniteIto.Universal 𝓕 μ H J)(hlocal:StandardTerminalPastLocality J)
    (hΛ:0≤Λ)(hbH:b≤H)(hb1:(b:ℝ)≤1)(hvb':v<b)
    (w:ℝ)(a:ℂ→L[ℝ]ℝ)(l:ℤ)(k:ℕ):
    ∃input:Process (E:=Both RealHaarInput) 𝓕 μ H,
      J.integral input=ᵐ[μ] (fun ω=>w*a (fourierCoeff
        (fun x:HeatCircle=>(RootSectionAverage.average R₀ k (Noise k) (ω,x):ℂ)) l)) ∧
      ∀ᵐz∂energyMeasure μ H,∀ℓ:Both RealHaarInput→L[ℝ]ℝ,
        ℓ (input z)=∫x:HeatCircle,NativeScalarFourierWeight.value w a l x*
          RootSectionAverage.average R₀ k (Coord k ℓ) (z,x) ∂AddCircle.haarAddCircle:=by
  obtain ⟨input,hI,hr⟩:=original_input_weighted
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
    P hAs θ v b hvb Z htarget hstop F hF hFm hsmall J hIJ₀ hIJ₁ hrootStop hrootTarget hcenter
    hnull hJ hlocal hΛ hbH hb1 hvb'
    (NativeScalarFourierWeight.value w a l) (NativeScalarFourierWeight.measurable w a l)
    ⟨‖w‖*‖a‖,mul_nonneg (norm_nonneg _) (norm_nonneg _)⟩
    (NativeScalarFourierWeight.bound w a l) k
  refine ⟨input,hI.trans (ae_of_all _ (fun ω=>?_)),hr⟩
  exact NativeScalarFourierWeight.integral _
    (RootDensityHistory.average_integrable R₀ AddCircle.haarAddCircle k (Noise k) ω
      (noise_integrable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
        P hAs θ v b hvb Z htarget hstop F hF hFm hΛ AddCircle.haarAddCircle k ω)) w a l
end SHE.MixedCanonicalWeightedPhysicalCoordinates
