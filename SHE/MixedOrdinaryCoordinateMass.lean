module
public import SHE.MixedOrdinaryWeightedPhysicalCoordinates
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
set_option quotPrecheck false
namespace SHE.MixedOrdinaryCoordinateMass
open Set MeasureTheory PredictableL2 StoppedFourier WordRecursion ControlledProfile ControlledReferenceLevel
  CutoffWordLevel CutoffWordHistories SmoothCylinders UniformSmooth OrthogonalItoChannels FiniteHaar DyadicApproximation
  NativeHeatObservation NativeObservationNaturality
open scoped NNReal ENNReal
local instance mixedOrdinaryCoordinateMass_period:Fact (0<2*Real.pi):=⟨by positivity⟩
local instance mixedOrdinaryCoordinateMass_sigma:MeasurableSpace CircleL2:=borel _
local instance mixedOrdinaryCoordinateMass_borel:BorelSpace CircleL2:=⟨rfl⟩
local instance mixedOrdinaryCoordinateMass_realSigma:MeasurableSpace RealL2:=borel _
local instance mixedOrdinaryCoordinateMass_realBorel:BorelSpace RealL2:=⟨rfl⟩
local instance mixedOrdinaryCoordinateMass_rowSigma:MeasurableSpace RealHaarInput:=borel _
local instance mixedOrdinaryCoordinateMass_rowBorel:BorelSpace RealHaarInput:=⟨rfl⟩
local instance mixedOrdinaryCoordinateMass_blockSigma:MeasurableSpace (Both RealHaarInput):=borel _
local instance mixedOrdinaryCoordinateMass_blockBorel:BorelSpace (Both RealHaarInput):=⟨rfl⟩
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
local notation "ht"=>(fun x (i:Fin 1)=>by simpa only [Subsingleton.elim i 0,htarget] using (le_refl (b:ℝ)))
local notation "hs"=>(fun x (i:Fin 1)=>by simpa only [Subsingleton.elim i 0,hstop] using (le_refl (b:ℝ)))
variable (F:HeatCircle→WordRecursion.State 1→ℝ)(hF:UniformBoundedSmooth F)
variable (hFm:Measurable (fun q:HeatCircle×WordRecursion.State 1=>F q.1 q.2))
local notation "Base"=>ControlledReferenceFamilyLevel.level P (fun z=>κ+aV z) hAs Λ θ v b hvb Z ht hs F hF hFm
local notation "R₀"=>referenceData P (fun z=>κ+aV z) hAs Λ θ v b hvb (0,0)
local notation "pastParameter"=>MixedNativeRandomReferenceStep.randomParameter 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S v
local notation "Raw"=>(fun k p=>OrdinaryUncutPhysicalGradient.raw modelU (Base p) k)

/-- One actual energy event controls every real-linear coordinate in the original history measure. -/
theorem coordinates_integrable(hbH:b≤H)(hb1:(b:ℝ)≤1)
    (ν:Measure HeatCircle)[IsFiniteMeasure ν](k:ℕ):
    ∀ᵐz∂energyMeasure μ H,∀ℓ:Both RealHaarInput→L[ℝ]ℝ,
      Integrable (fun h=>ℓ (Raw k (pastParameter z.2) (h,z))) (historyMeasure R₀ ν k):=by
  letI:IsFiniteMeasure (energyMeasure μ H):=by dsimp only [energyMeasure];infer_instance
  obtain ⟨B,hBi,hB⟩:=ControlledOrdinaryPhysicalSections.uniform_integrable_bound
    P (fun z=>κ+aV z) hAs Λ θ v b hvb Z ht hs F hF hFm modelU k hbH hb1 ν
  have hm(p:Inputs):Measurable (Raw k p):=by
    have hh:=OrdinaryUncutPhysicalGradient.raw_predictable modelU (Base p) k
    have hmap:@Measurable (History HeatCircle k×(ℝ≥0×Ω)) (History HeatCircle k×(ℝ≥0×Ω)) inferInstance
        ((inferInstance:MeasurableSpace (History HeatCircle k)).prod 𝓕.predictable) id:=
      measurable_fst.prodMk (measurable_snd.mono le_rfl (predictable_le_product 𝓕))
    exact hh.comp hmap
  filter_upwards [hBi.prod_left_ae] with z hz ℓ
  exact ℓ.integrable_comp (hz.mono'
    ((hm (pastParameter z.2)).comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable
    (ae_of_all _ (fun h=>hB (pastParameter z.2) (h,z))))
end SHE.MixedOrdinaryCoordinateMass
