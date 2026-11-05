module
public import SHE.MixedOrdinaryPhysicalCoordinates
public import SHE.RootDensityHistory
public import SHE.NativeScalarFourierWeight

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
set_option quotPrecheck false
namespace SHE.MixedOrdinaryWeightedPhysicalCoordinates
open Set MeasureTheory PredictableL2 StoppedFourier WordRecursion ControlledProfile ControlledReferenceLevel
  CutoffWordLevel CutoffWordHistories SmoothCylinders UniformSmooth OrthogonalItoChannels FiniteHaar DyadicApproximation
  NativeHeatObservation NativeObservationNaturality
open scoped NNReal ENNReal
local instance mixedOrdinaryPhysicalCoordinates_period:Fact (0<2*Real.pi):=⟨by positivity⟩
local instance mixedOrdinaryPhysicalCoordinates_sigma:MeasurableSpace CircleL2:=borel _
local instance mixedOrdinaryPhysicalCoordinates_borel:BorelSpace CircleL2:=⟨rfl⟩
local instance mixedOrdinaryPhysicalCoordinates_realSigma:MeasurableSpace RealL2:=borel _
local instance mixedOrdinaryPhysicalCoordinates_realBorel:BorelSpace RealL2:=⟨rfl⟩
local instance mixedOrdinaryPhysicalCoordinates_rowSigma:MeasurableSpace RealHaarInput:=borel _
local instance mixedOrdinaryPhysicalCoordinates_rowBorel:BorelSpace RealHaarInput:=⟨rfl⟩
local instance mixedOrdinaryPhysicalCoordinates_blockSigma:MeasurableSpace (Both RealHaarInput):=borel _
local instance mixedOrdinaryPhysicalCoordinates_blockBorel:BorelSpace (Both RealHaarInput):=⟨rfl⟩
variable {Ω:Type}[MeasurableSpace Ω]
variable (𝓕:Filtration ℝ≥0 ‹MeasurableSpace Ω›)(μ:Measure Ω)[IsProbabilityMeasure μ](H:ℝ≥0)
variable (Λ κ:ℝ)(hκ:0<κ){aU aV:ℝ→ℝ}(haU:Measurable aU)(haV:Measurable aV){ell M:ℝ}
variable (hell:0<ell)(hbU:∀z,ell≤aU z∧aU z≤M)(hbV:∀z,ell≤aV z∧aV z≤M)
variable (I₀ I₁:StandardTerminalIto (C:=RealHaarIntegrand.Columns) (E:=RealL2) 𝓕 μ H)
variable (u₀ v₀:RealL2)
variable (S:MixedNativeAdditiveResidualPair.Solution 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀)
variable (J:StandardTerminalIto (C:=Both RealHaarInput) (E:=ℝ) 𝓕 μ H)
variable (hIJ₀:StandardScalarNaturality I₀ (leftIntegral 𝓕 μ H J))
variable (hIJ₁:StandardScalarNaturality I₁ (rightIntegral 𝓕 μ H J))
variable (hnull:NullCompleteFiltration.ContainsNullSets 𝓕 μ)(hJ:StandardFiniteIto.Universal 𝓕 μ H J)
local notation "modelU"=>MixedNativeOrdinaryModel.model 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S J hIJ₀ hIJ₁ hnull hJ
variable (P:CanonicalCovariance.ProfileParameters)(hAs:BoundedSmooth (fun z=>κ+aV z))
variable (θ:ℝ)(v b:ℝ≥0)(hvb:v≤b)
variable (Z:VariableObservations.Family HeatCircle 1)
variable (hstop:∀x,(Z.observations x 0).stop=(b:ℝ))(htarget:∀x,(Z.observations x 0).target=(b:ℝ))
variable (hcenter:∀x,(Z.observations x 0).center=x)
local notation "ht"=>(fun x (i:Fin 1)=>by simpa only [Subsingleton.elim i 0,htarget] using (le_refl (b:ℝ)))
local notation "hs"=>(fun x (i:Fin 1)=>by simpa only [Subsingleton.elim i 0,hstop] using (le_refl (b:ℝ)))
variable (F:HeatCircle→WordRecursion.State 1→ℝ)(hF:UniformBoundedSmooth F)
variable (hFm:Measurable (fun q:HeatCircle×WordRecursion.State 1=>F q.1 q.2))
local notation "Base"=>ControlledReferenceFamilyLevel.level P (fun z=>κ+aV z) hAs Λ θ v b hvb Z ht hs F hF hFm
local notation "R₀"=>referenceData P (fun z=>κ+aV z) hAs Λ θ v b hvb (0,0)
local notation "pastParameter"=>MixedNativeRandomReferenceStep.randomParameter 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S v
local notation "Raw"=>(fun k p=>OrdinaryUncutPhysicalGradient.raw modelU (Base p) k)
variable (hsmall:ProfileStability.memoryConstant P.lower P.holder P.exponent*
  ProfileVolterra.powerConstant ((P.exponent-2)/4)*P.horizon^(P.exponent/4)≤1/2)

local notation "Noise"=>(fun k (z:Ω×History HeatCircle k)=>
  OrdinaryUncutNoise.value modelU (Base (pastParameter z.1)) k z.2 z.1)
local notation "Coord"=>(fun k (ℓ:Both RealHaarInput→L[ℝ]ℝ) (z:(ℝ≥0×Ω)×History HeatCircle k)=>
  OrdinaryPhysicalCoordinates.coordinate modelU (Base (pastParameter z.1.2)) k ℓ (z.2,z.1))

def noiseField(k:ℕ)(z:Ω×HeatCircle):ℝ:=RootSectionAverage.average R₀ k (Noise k) z

def coordinateField(k:ℕ)(ℓ:Both RealHaarInput→L[ℝ]ℝ)(z:(ℝ≥0×Ω)×HeatCircle):ℝ:=
  RootSectionAverage.average R₀ k (Coord k ℓ) z

local notation "NF"=>noiseField 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S J hIJ₀ hIJ₁ hnull hJ
  P hAs θ v b hvb Z hstop htarget F hF hFm
local notation "CF"=>coordinateField 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S J hIJ₀ hIJ₁ hnull hJ
  P hAs θ v b hvb Z hstop htarget F hF hFm

private theorem noise_integrable(ν:Measure HeatCircle)[IsFiniteMeasure ν](k:ℕ)(ω:Ω):
    Integrable (fun h=>Noise k (ω,h)) (historyMeasure R₀ ν k):=by
  obtain ⟨C,hC,hCb⟩:=ControlledOrdinaryNoise.value_bound
    P (fun z=>κ+aV z) hAs Λ θ v b hvb Z ht hs F hF hFm modelU k
  have hm:Measurable (fun h:History HeatCircle k=>Noise k (ω,h)):=
    (OrdinaryUncutNoise.value_measurable modelU (Base (pastParameter ω)) k).comp
      (measurable_id.prodMk measurable_const)
  exact ((UncutHistoryMass.weight_integrable (Base (0,0)) ν k).const_mul C).mono'
    hm.aestronglyMeasurable (ae_of_all _ (fun h=>hCb (pastParameter ω) h ω))

include hIJ₀ hIJ₁ hnull hJ hstop htarget hcenter hsmall in
/-- Positive root tests retain the actual pure-U original-J output and
one current/sample event for every physical continuous-linear coordinate. -/
theorem original_input_density(hlocal:StandardTerminalPastLocality J)(hΛ:0≤Λ)(hbH:b≤H)(hb1:(b:ℝ)≤1)
    (hvb':v<b)(g:HeatCircle→ℝ)(hg:Measurable g)(B:ℝ≥0)
    (hg0:∀x,0≤g x)(hgB:∀x,g x≤B)(k:ℕ):
    ∃input:Process (E:=Both RealHaarInput) 𝓕 μ H,
      (∀ω,Integrable (fun x:HeatCircle=>g x*NF k (ω,x)) AddCircle.haarAddCircle)∧
      J.integral input=ᵐ[μ] (fun ω=>∫x:HeatCircle,g x*NF k (ω,x) ∂AddCircle.haarAddCircle)∧
      ∀ᵐz∂energyMeasure μ H,∀ℓ:Both RealHaarInput→L[ℝ]ℝ,
        Integrable (fun x:HeatCircle=>g x*CF k ℓ (z,x)) AddCircle.haarAddCircle∧
        ℓ (input z)=∫x:HeatCircle,g x*CF k ℓ (z,x) ∂AddCircle.haarAddCircle:=by
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
  letI:IsFiniteMeasure (energyMeasure μ H):=by dsimp only [energyMeasure];infer_instance
  obtain ⟨input,hout,hcoord⟩:=MixedOrdinaryPhysicalCoordinates.original_input
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S J hIJ₀ hIJ₁ hnull hJ
    P hAs θ v b hvb Z hstop htarget hcenter F hF hFm hsmall hlocal hΛ hbH hb1 hvb' ν B hν k
  obtain ⟨E,hEi,hE⟩:=ControlledOrdinaryPhysicalSections.uniform_integrable_bound
    P (fun z=>κ+aV z) hAs Λ θ v b hvb Z ht hs F hF hFm modelU k hbH hb1 ν
  have hm(p:Inputs):Measurable (Raw k p):=by
    have hh:=OrdinaryUncutPhysicalGradient.raw_predictable modelU (Base p) k
    have hmap:@Measurable (History HeatCircle k×(ℝ≥0×Ω)) (History HeatCircle k×(ℝ≥0×Ω)) inferInstance
        ((inferInstance:MeasurableSpace (History HeatCircle k)).prod 𝓕.predictable) id:=
      measurable_fst.prodMk (measurable_snd.mono le_rfl (predictable_le_product 𝓕))
    exact hh.comp hmap
  refine ⟨input,?_,?_,?_⟩
  · intro ω
    exact RootDensityHistory.integrable R₀ k g hg hg0 (Noise k) ω
      (noise_integrable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S J hIJ₀ hIJ₁ hnull hJ
        P hAs θ v b hvb Z hstop htarget F hF hFm ν k ω)
  · refine hout.trans (ae_of_all _ (fun ω=>?_))
    exact RootDensityHistory.integral R₀ k g hg hg0 (Noise k) ω
      (noise_integrable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S J hIJ₀ hIJ₁ hnull hJ
        P hAs θ v b hvb Z hstop htarget F hF hFm ν k ω)
  · filter_upwards [hcoord,hEi.prod_left_ae] with z hz hzi ℓ
    have hr:Integrable (fun h=>Raw k (pastParameter z.2) (h,z)) (historyMeasure R₀ ν k):=
      hzi.mono' ((hm (pastParameter z.2)).comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable
        (ae_of_all _ (fun h=>hE (pastParameter z.2) (h,z)))
    have hc:Integrable (fun h=>Coord k ℓ (z,h)) (historyMeasure R₀ ν k):=
      (ℓ.integrable_comp hr).congr (ae_of_all _ (fun h=>
        OrdinaryPhysicalCoordinates.coordinate_eq modelU (Base (pastParameter z.2)) k ℓ (h,z)))
    refine ⟨RootDensityHistory.integrable R₀ k g hg hg0 (Coord k ℓ) z hc,?_⟩
    rw [hz ℓ]
    exact RootDensityHistory.integral R₀ k g hg hg0 (Coord k ℓ) z hc

include hIJ₀ hIJ₁ hnull hJ hstop htarget hcenter hsmall in
/-- Every bounded signed root test keeps the SAME original J and all
physical coordinates, with the original old-time/space measures. -/
theorem original_input_weighted(hlocal:StandardTerminalPastLocality J)(hΛ:0≤Λ)(hbH:b≤H)(hb1:(b:ℝ)≤1)
    (hvb':v<b)(g:HeatCircle→ℝ)(hg:Measurable g)(B:ℝ≥0)(hgB:∀x,‖g x‖≤B)(k:ℕ):
    ∃input:Process (E:=Both RealHaarInput) 𝓕 μ H,
      J.integral input=ᵐ[μ] (fun ω=>∫x:HeatCircle,g x*NF k (ω,x) ∂AddCircle.haarAddCircle)∧
      ∀ᵐz∂energyMeasure μ H,∀ℓ:Both RealHaarInput→L[ℝ]ℝ,
        ℓ (input z)=∫x:HeatCircle,g x*CF k ℓ (z,x) ∂AddCircle.haarAddCircle:=by
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
  obtain ⟨ip,hipI,hip,hcp⟩:=original_input_density
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S J hIJ₀ hIJ₁ hnull hJ
    P hAs θ v b hvb Z hstop htarget hcenter F hF hFm hsmall hlocal hΛ hbH hb1 hvb'
    gp hgp B (fun _=>le_max_right _ _) hgpB k
  obtain ⟨ineg,hinI,hin,hcn⟩:=original_input_density
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S J hIJ₀ hIJ₁ hnull hJ
    P hAs θ v b hvb Z hstop htarget hcenter F hF hFm hsmall hlocal hΛ hbH hb1 hvb'
    gn hgn B (fun _=>le_max_right _ _) hgnB k
  have hmass(f:HeatCircle→ℝ)(hp:Integrable (fun x=>gp x*f x) AddCircle.haarAddCircle)
      (hn:Integrable (fun x=>gn x*f x) AddCircle.haarAddCircle):
      (∫x,gp x*f x ∂AddCircle.haarAddCircle)-(∫x,gn x*f x ∂AddCircle.haarAddCircle)=
        ∫x,g x*f x ∂AddCircle.haarAddCircle:=by
    rw [←integral_sub hp hn]
    apply integral_congr_ae
    filter_upwards with x
    change gp x*f x-gn x*f x=g x*f x
    rw [←sub_mul,hdiff]
  refine ⟨ip-ineg,?_,?_⟩
  · have hsub:J.integral (ip-ineg)=J.integral ip-J.integral ineg:=map_sub J.integral ip ineg
    have ha:=Lp.coeFn_sub (J.integral ip) (J.integral ineg)
    rw [←hsub] at ha
    filter_upwards [hip,hin,ha] with ω hp hn hh
    rw [hh,Pi.sub_apply,hp,hn]
    exact hmass _ (hipI ω) (hinI ω)
  · have ha:=ae_eq_of_ae_eq_trim (Lp.coeFn_sub ip ineg)
    filter_upwards [hcp,hcn,ha] with z hp hn hz ℓ
    change ℓ ((ip-ineg) z)=_
    rw [hz]
    change ℓ (ip z-ineg z)=_
    rw [map_sub,(hp ℓ).2,(hn ℓ).2]
    exact hmass _ (hp ℓ).1 (hn ℓ).1

include hIJ₀ hIJ₁ hnull hJ hstop htarget hcenter hsmall in
/-- The actual Fourier output and every raw coordinate belong to the
same original-J input after the genuine pure-U past substitution. -/
theorem original_input_fourier(hlocal:StandardTerminalPastLocality J)(hΛ:0≤Λ)(hbH:b≤H)(hb1:(b:ℝ)≤1)
    (hvb':v<b)(w:ℝ)(a:ℂ→L[ℝ]ℝ)(l:ℤ)(k:ℕ):
    ∃input:Process (E:=Both RealHaarInput) 𝓕 μ H,
      J.integral input=ᵐ[μ] (fun ω=>w*a (fourierCoeff (fun x:HeatCircle=>(NF k (ω,x):ℂ)) l))∧
      ∀ᵐz∂energyMeasure μ H,∀ℓ:Both RealHaarInput→L[ℝ]ℝ,
        ℓ (input z)=∫x:HeatCircle,NativeScalarFourierWeight.value w a l x*CF k ℓ (z,x) ∂AddCircle.haarAddCircle:=by
  obtain ⟨input,hout,hcoord⟩:=original_input_weighted
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S J hIJ₀ hIJ₁ hnull hJ
    P hAs θ v b hvb Z hstop htarget hcenter F hF hFm hsmall hlocal hΛ hbH hb1 hvb'
    (NativeScalarFourierWeight.value w a l) (NativeScalarFourierWeight.measurable w a l)
    ⟨‖w‖*‖a‖,mul_nonneg (norm_nonneg _) (norm_nonneg _)⟩ (NativeScalarFourierWeight.bound w a l) k
  refine ⟨input,hout.trans (ae_of_all _ (fun ω=>?_)),hcoord⟩
  exact NativeScalarFourierWeight.integral _
    (RootDensityHistory.average_integrable R₀ AddCircle.haarAddCircle k (Noise k) ω
      (noise_integrable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S J hIJ₀ hIJ₁ hnull hJ
        P hAs θ v b hvb Z hstop htarget F hF hFm AddCircle.haarAddCircle k ω)) w a l

end SHE.MixedOrdinaryWeightedPhysicalCoordinates

