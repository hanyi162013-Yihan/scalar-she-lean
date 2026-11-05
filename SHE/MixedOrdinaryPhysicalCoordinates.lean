module
public import SHE.MixedOrdinaryRawPastInput
public import SHE.OrdinaryPhysicalCoordinates

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
set_option quotPrecheck false
namespace SHE.MixedOrdinaryPhysicalCoordinates
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

include hIJ₀ hIJ₁ hnull hJ hstop htarget hcenter hsmall in
/-- One original current/sample event works for EVERY continuous-linear
coordinate of the genuine random-past PURE-U original-J input. -/
theorem original_input(hlocal:StandardTerminalPastLocality J)(hΛ:0≤Λ)(hbH:b≤H)(hb1:(b:ℝ)≤1)
    (hvb':v<b)(ν:Measure HeatCircle)[IsFiniteMeasure ν](c:ℝ≥0)
    (hν:ν≤(c:ℝ≥0∞) • (AddCircle.haarAddCircle:Measure HeatCircle))(k:ℕ):
    ∃input:Process (E:=Both RealHaarInput) 𝓕 μ H,
      J.integral input=ᵐ[μ] (fun ω=>ControlledOrdinaryAverage.average P (fun z=>κ+aV z) hAs Λ θ v b hvb
        Z ht hs F hF hFm modelU ν (pastParameter ω) k ω)∧
      ∀ᵐz∂energyMeasure μ H,∀ℓ:Both RealHaarInput→L[ℝ]ℝ,
        ℓ (input z)=∫h,OrdinaryPhysicalCoordinates.coordinate modelU
          (Base (pastParameter z.2)) k ℓ (h,z) ∂historyMeasure R₀ ν k:=by
  letI:IsFiniteMeasure (energyMeasure μ H):=by dsimp only [energyMeasure];infer_instance
  obtain ⟨input,hi,hout⟩:=MixedOrdinaryRawPastInput.original_input
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S J hIJ₀ hIJ₁ hnull hJ
    P hAs θ v b hvb Z hstop htarget hcenter F hF hFm hsmall hlocal hΛ hbH hb1 hvb' ν c hν k
  obtain ⟨B,hBi,hB⟩:=ControlledOrdinaryPhysicalSections.uniform_integrable_bound
    P (fun z=>κ+aV z) hAs Λ θ v b hvb Z ht hs F hF hFm modelU k hbH hb1 ν
  have hm(p:Inputs):Measurable (Raw k p):=by
    have hraw:=OrdinaryUncutPhysicalGradient.raw_predictable modelU (Base p) k
    have hmap:@Measurable (History HeatCircle k×(ℝ≥0×Ω)) (History HeatCircle k×(ℝ≥0×Ω)) inferInstance
        ((inferInstance:MeasurableSpace (History HeatCircle k)).prod 𝓕.predictable) id:=
      measurable_fst.prodMk (measurable_snd.mono le_rfl (predictable_le_product 𝓕))
    exact hraw.comp hmap
  refine ⟨input,hout,?_⟩
  filter_upwards [hi,hBi.prod_left_ae] with z hz hzi ℓ
  have hr:Integrable (fun h=>Raw k (pastParameter z.2) (h,z)) (historyMeasure R₀ ν k):=
    hzi.mono' ((hm (pastParameter z.2)).comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable
      (ae_of_all _ (fun h=>hB (pastParameter z.2) (h,z)))
  rw [hz,←ℓ.integral_comp_comm hr]
  apply integral_congr_ae
  filter_upwards with h
  exact OrdinaryPhysicalCoordinates.coordinate_eq modelU (Base (pastParameter z.2)) k ℓ (h,z)

end SHE.MixedOrdinaryPhysicalCoordinates
