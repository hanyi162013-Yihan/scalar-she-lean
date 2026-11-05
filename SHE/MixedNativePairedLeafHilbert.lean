module
public import SHE.NativeBesselSectionEnergy
public import SHE.MixedNativePairedLeafAverage
public import SHE.MixedNativePairedHilbertExpansion
public import SHE.MixedNativePairedLeafIdentification
public import SHE.NativeBesselDifferenceIdentity
public import SHE.ControlledPairedUncutLeafIdentity
public import SHE.MixedPastTerminalEndpointWord
public import SHE.RootSectionLinear
public import SHE.MixedOrdinaryRootHilbertExpansion
public import SHE.MixedCanonicalRootHilbertExpansion
public import SHE.MixedNativeHigherOriginalEnergy
public import SHE.MixedNativePairedOriginalInput
public import SHE.MixedNativeOriginalFourierRows
public import SHE.MixedPastNativeCompleteSections
public import SHE.NativeOriginalRowsEnergy
public import SHE.MixedCanonicalNoiseIncrement
public import SHE.MixedOrdinaryNoiseHilbert
public import SHE.MixedOrdinaryCoordinateMass
public import SHE.MixedNativeColumnRawFourier
public import SHE.RootSectionLinear
public import SHE.NativeMultiplierFourierIntegral

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2600000
set_option quotPrecheck false
namespace SHE.MixedNativePairedLeafHilbert
open Set MeasureTheory PredictableL2 StoppedFourier WordRecursion ControlledProfile ControlledReferenceLevel
  CutoffWordLevel CutoffWordHistories SmoothCylinders UniformSmooth OrthogonalItoChannels FiniteHaar DyadicApproximation
  NativeHeatObservation NativeObservationNaturality
open scoped NNReal ENNReal
local instance mixedNativePairedOriginalInput_period:Fact (0<2*Real.pi):=⟨by positivity⟩
local instance mixedNativePairedOriginalInput_sigma:MeasurableSpace CircleL2:=borel _
local instance mixedNativePairedOriginalInput_borel:BorelSpace CircleL2:=⟨rfl⟩
local instance mixedNativePairedOriginalInput_realSigma:MeasurableSpace RealL2:=borel _
local instance mixedNativePairedOriginalInput_realBorel:BorelSpace RealL2:=⟨rfl⟩
local instance mixedNativePairedOriginalInput_rowSigma:MeasurableSpace RealHaarInput:=borel _
local instance mixedNativePairedOriginalInput_rowBorel:BorelSpace RealHaarInput:=⟨rfl⟩
local instance mixedNativePairedOriginalInput_blockSigma:MeasurableSpace (Both RealHaarInput):=borel _
local instance mixedNativePairedOriginalInput_blockBorel:BorelSpace (Both RealHaarInput):=⟨rfl⟩
variable {Ω:Type}[MeasurableSpace Ω]
variable (𝓕:Filtration ℝ≥0 ‹MeasurableSpace Ω›)(μ:Measure Ω)[IsProbabilityMeasure μ](H:ℝ≥0)
variable (Λ κ:ℝ)(hκ:0<κ){aU aV:ℝ→ℝ}(haU:Measurable aU)(haV:Measurable aV){ell M:ℝ}
variable (hell:0<ell)(hbU:∀z,ell≤aU z∧aU z≤M)(hbV:∀z,ell≤aV z∧aV z≤M)
variable (I₀ I₁:StandardTerminalIto (C:=RealHaarIntegrand.Columns) (E:=RealL2) 𝓕 μ H)
variable (u₀:RealL2)
variable (S:MixedNativeAdditiveResidualPair.Solution 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀)
variable (J:StandardTerminalIto (C:=Both RealHaarInput) (E:=ℝ) 𝓕 μ H)
variable (hIJ₀:StandardScalarNaturality I₀ (leftIntegral 𝓕 μ H J))
variable (hIJ₁:StandardScalarNaturality I₁ (rightIntegral 𝓕 μ H J))
variable (hnull:NullCompleteFiltration.ContainsNullSets 𝓕 μ)(hJ:StandardFiniteIto.Universal 𝓕 μ H J)
local notation "modelU"=>MixedNativeOrdinaryModel.model 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S J hIJ₀ hIJ₁ hnull hJ
variable (P:CanonicalCovariance.ProfileParameters)(haP:BoundedSmooth P.coefficient)
variable (hAs:BoundedSmooth (fun z=>κ+aV z))
variable (v b:ℝ≥0)(hvb:v≤b)(Z:VariableObservations.Family HeatCircle 1)
variable (hrootStop:∀x,(Z.observations x 0).stop=(b:ℝ))
variable (hrootTarget:∀x,(Z.observations x 0).target=(b:ℝ))
variable (hcenter:∀x,(Z.observations x 0).center=x)
local notation "ht"=>(fun x (i:Fin 1)=>by simpa only [Subsingleton.elim i 0,hrootTarget] using (le_refl (b:ℝ)))
local notation "hs"=>(fun x (i:Fin 1)=>by simpa only [Subsingleton.elim i 0,hrootStop] using (le_refl (b:ℝ)))
variable (F:HeatCircle→WordRecursion.State 1→ℝ)(hF:UniformBoundedSmooth F)
variable (hFm:Measurable (fun z:HeatCircle×WordRecursion.State 1=>F z.1 z.2))
local notation "R₀"=>referenceData P P.coefficient haP Λ 0 v b hvb (0,0)
local notation "R1"=>referenceData P (fun z=>κ+aV z) hAs Λ 1 v b hvb (0,0)
local notation "R0"=>referenceData P (fun z=>κ+aV z) hAs Λ 0 v b hvb (0,0)
local notation "Base1"=>ControlledReferenceFamilyLevel.level P (fun z=>κ+aV z) hAs Λ 1 v b hvb Z ht hs F hF hFm
local notation "Base0"=>ControlledReferenceFamilyLevel.level P (fun z=>κ+aV z) hAs Λ 0 v b hvb Z ht hs F hF hFm
local notation "pastParameter"=>MixedNativeRandomReferenceStep.randomParameter 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S v




local notation "JF"=>MixedCanonicalRootFields.field 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S P hAs 1 v b hvb Z ht hs F hF hFm
local notation "OF"=>MixedOrdinaryRootFields.field 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S J hIJ₀ hIJ₁ hnull hJ P hAs 0 v b hvb Z hrootStop hrootTarget F hF hFm
local notation "Field"=>MixedNativePairedLeafAverage.field 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP v b hvb Z hrootStop hrootTarget F hF hFm
variable (hsmall:ProfileStability.memoryConstant P.lower P.holder P.exponent*
  ProfileVolterra.powerConstant ((P.exponent-2)/4)*P.horizon^(P.exponent/4)≤1/2)

include hsmall J hIJ₀ hIJ₁ hnull hJ hAs in
theorem field_measurable(hA:P.coefficient=(fun z=>κ+aV z))(hΛ:0≤Λ)(k:ℕ):Measurable (Field k):=by
  have he:Field k=(fun z=>JF 0 k z-OF 0 k z):=by
    funext z
    exact MixedNativePairedLeafAverage.field_difference 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S J hIJ₀ hIJ₁ hnull hJ P haP hAs v b hvb Z hrootStop hrootTarget F hF hFm hsmall hA hΛ k z.1 z.2
  rw [he]
  exact (MixedCanonicalRootFields.field_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S P hAs 1 v b hvb Z ht hs F hF hFm hsmall hΛ 0 k).sub
    (MixedOrdinaryRootFields.field_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S J hIJ₀ hIJ₁ hnull hJ P hAs 0 v b hvb Z hrootStop hrootTarget F hF hFm hsmall hΛ 0 k)

variable (hL:1≤Λ){ρ:ℝ}(hρ:0≤ρ)

include hsmall J hIJ₀ hIJ₁ hnull hJ hAs hL hρ in
theorem section_memLp(hA:P.coefficient=(fun z=>κ+aV z))(k:ℕ)(ω:Ω):
    MemLp (fun x:HeatCircle=>(Field k (ω,x):ℂ)) 2 AddCircle.haarAddCircle:=by
  have hj:=MixedCanonicalRootHilbertExpansion.field_section_memLp 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S P hAs 1 v b hvb Z ht hs F hF hFm hsmall hL hρ 0 k ω
  have ho:=MixedOrdinaryRootFields.section_memLp 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S J hIJ₀ hIJ₁ hnull hJ P hAs 0 v b hvb Z hrootStop hrootTarget F hF hFm hsmall (zero_le_one.trans hL) 0 k ω
  convert hj.sub ho using 1
  ext x
  simp only [MixedNativePairedLeafAverage.field_difference 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S J hIJ₀ hIJ₁ hnull hJ P haP hAs v b hvb Z hrootStop hrootTarget F hF hFm hsmall hA (zero_le_one.trans hL),
    Complex.ofReal_sub,Pi.sub_apply]

include hsmall in
/-- The exact leaf of the finite native paired expansion is the actual
native Bessel image of the original retained-root terminal-word difference.
Both scalar/history and spatial L2 applicability are established. -/
theorem leaf_eq_native(hA:P.coefficient=(fun z=>κ+aV z))(k:ℕ)(ω:Ω):
    MixedNativePairedHilbertExpansion.leaf 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S J hIJ₀ hIJ₁ hnull hJ P hAs v b hvb Z hrootStop hrootTarget F hF hFm hL hρ k ω=
      NativeBesselFieldAE.value Λ ρ hL hρ (fun z:Ω×HeatCircle=>(Field k z:ℂ)) ω:=by
  have hf:=field_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S J hIJ₀ hIJ₁ hnull hJ P haP hAs v b hvb Z hrootStop hrootTarget F hF hFm hsmall hA (zero_le_one.trans hL) k
  have hj:=MixedCanonicalRootFields.field_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S P hAs 1 v b hvb Z ht hs F hF hFm hsmall (zero_le_one.trans hL) 0 k
  have ho:=MixedOrdinaryRootFields.field_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S J hIJ₀ hIJ₁ hnull hJ P hAs 0 v b hvb Z hrootStop hrootTarget F hF hFm hsmall (zero_le_one.trans hL) 0 k
  have hid:∀ᵐx∂AddCircle.haarAddCircle,(Field k (ω,x):ℂ)=(JF 0 k (ω,x):ℂ)-(OF 0 k (ω,x):ℂ):=by
    apply ae_of_all
    intro x
    rw [MixedNativePairedLeafAverage.field_difference 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S J hIJ₀ hIJ₁ hnull hJ P haP hAs v b hvb Z hrootStop hrootTarget F hF hFm hsmall hA (zero_le_one.trans hL)]
    exact Complex.ofReal_sub _ _
  have hn:=NativeBesselDifferenceIdentity.sub Λ ρ hL hρ _ _ _
    (Complex.continuous_ofReal.measurable.comp hf) (Complex.continuous_ofReal.measurable.comp hj)
    (Complex.continuous_ofReal.measurable.comp ho) ω
    (section_memLp 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S J hIJ₀ hIJ₁ hnull hJ P haP hAs v b hvb Z hrootStop hrootTarget F hF hFm hsmall hL hρ hA k ω)
    (MixedCanonicalRootHilbertExpansion.field_section_memLp 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S P hAs 1 v b hvb Z ht hs F hF hFm hsmall hL hρ 0 k ω)
    (MixedOrdinaryRootFields.section_memLp 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S J hIJ₀ hIJ₁ hnull hJ P hAs 0 v b hvb Z hrootStop hrootTarget F hF hFm hsmall (zero_le_one.trans hL) 0 k ω) hid
  exact hn.symm

include hsmall in
/-- Any actual Borel scalar section identified with the original paired
terminal words has the SAME native Hilbert leaf, with no new L2 premise. -/
theorem native_eq_of_section(hA:P.coefficient=(fun z=>κ+aV z))
    (Y:Ω×HeatCircle→ℝ)(hY:Measurable Y)(k:ℕ)(ω:Ω)
    (he:∀ᵐx∂AddCircle.haarAddCircle,Y (ω,x)=Field k (ω,x)):
    NativeBesselFieldAE.value Λ ρ hL hρ (fun z:Ω×HeatCircle=>(Y z:ℂ)) ω=
      MixedNativePairedHilbertExpansion.leaf 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S J hIJ₀ hIJ₁ hnull hJ P hAs v b hvb Z hrootStop hrootTarget F hF hFm hL hρ k ω:=by
  rw [leaf_eq_native 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S J hIJ₀ hIJ₁ hnull hJ P haP hAs v b hvb Z hrootStop hrootTarget F hF hFm hsmall hL hρ hA k ω]
  have hc:∀ᵐx∂AddCircle.haarAddCircle,(Y (ω,x):ℂ)=(Field k (ω,x):ℂ):=
    he.mono (fun x hx=>congrArg (fun r:ℝ=>(r:ℂ)) hx)
  have hg:=section_memLp 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S J hIJ₀ hIJ₁ hnull hJ P haP hAs v b hvb Z hrootStop hrootTarget F hF hFm hsmall hL hρ hA k ω
  exact NativeBesselSectionEnergy.congr Λ ρ hL hρ _ _
    (Complex.continuous_ofReal.measurable.comp hY)
    (Complex.continuous_ofReal.measurable.comp (field_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S J hIJ₀ hIJ₁ hnull hJ P haP hAs v b hvb Z hrootStop hrootTarget F hF hFm hsmall hA (zero_le_one.trans hL) k))
    ω ((memLp_congr_ae hc).mpr hg) hg hc

end SHE.MixedNativePairedLeafHilbert
