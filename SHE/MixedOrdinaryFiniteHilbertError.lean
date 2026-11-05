module
public import SHE.MixedOrdinaryErrorRootIdentity
public import SHE.NativeBesselFiniteSumEnergy
public import SHE.MixedOrdinaryErrorPrimitive
public import SHE.MixedOrdinaryFirstHit
public import SHE.MixedOrdinaryRootFields
public import SHE.ControlledActualTimeRemainder
public import SHE.MixedPastNewestUncutError
public import SHE.MixedPastNewestOriginalMass
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
namespace SHE.MixedOrdinaryFiniteHilbertError
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




local notation "Error"=>MixedOrdinaryRootFields.error 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S J hIJ₀ hIJ₁ hnull hJ P hAs 0 v b hvb Z hrootStop hrootTarget F hF hFm
local notation "Primitive"=>MixedPastNewestOrdinaryError.primitive 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP v b hvb Z ht hs F hF hFm
local notation "Rzero"=>referenceData P P.coefficient haP Λ 0 v b hvb (0,0)
local notation "Ages"=>MixedOrdinaryErrorPrimitive.ages b Z hrootStop hrootTarget
local notation "Upper"=>MixedOrdinaryErrorPrimitive.stopUpper b Z hrootStop
variable (hsmall:ProfileStability.memoryConstant P.lower P.holder P.exponent*
  ProfileVolterra.powerConstant ((P.exponent-2)/4)*P.horizon^(P.exponent/4)≤1/2)

variable (hL:1≤Λ){ρ:ℝ}(hρ:0≤ρ)
local notation "Discrepancy"=>MixedOrdinaryRootHilbertExpansion.discrepancy
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S J hIJ₀ hIJ₁ hnull hJ
  P hAs 0 v b hvb Z hrootStop hrootTarget F hF hFm hL hρ

include hsmall haP in
/-- The exact finite ordinary discrepancies occurring in the paired
native expansion satisfy the canonical vanishing coefficient-error
bound. Its constant is independent of the companion smoothing index. -/
theorem energy (hcoeff:P.coefficient=(fun z=>κ+aV z))
    (D:SmoothApproximation.ScalarData){h:ℝ}(hh:0<h)(hh1:h≤1)
    (hcontract:GaussianProfile.contractionConstant D.ell D.holderConstant D.beta*h^(D.beta/4)≤1/2)
    (j:ℕ)(hP:P=ControlledSmoothLimit.smoothTotalParameters D hh hh1 hcontract j)
    (hU:aU=D.residualCoefficient)(hV:aV=D.smoothCoefficient j)
    {B Hr:ℝ}(hB:0≤B)(hHr:0≤Hr)
    (hroot:∀x z,|F x z|≤B)
    (hrootmod:∀x z w,|F x z-F x w|≤Hr*|z 0-w 0|^P.exponent)
    (hlocal:StandardTerminalPastLocality J)
    (hspan:(b:ℝ)-(v:ℝ)≤P.horizon)(hvb':v<b)(hbH:b≤H)(depth:ℕ)
    (hold:∀i,i<depth→(b:ℝ)-(v:ℝ)≤PhysicalScoreChain.uniformHorizon 1 i)
    (A0 ν:ℝ)(hA:0≤A0)(hν:0≤ν)
    (hjet:∀x i,i≤depth→∀z,‖iteratedFDeriv ℝ i (F x) z‖≤A0*ν^i)
    (B0:ℕ→ℝ≥0)(hBDG:∀k,k<depth→StandardTerminalBDGPower (k+2) J (B0 k)):
    Integrable (fun ω=>‖∑k∈Finset.range depth,Discrepancy k ω‖^2) μ ∧
      (∫ω,‖∑k∈Finset.range depth,Discrepancy k ω‖^2 ∂μ)≤
        Λ^(-ρ)*(ScalarApproximationDiscrepancy.scalarError D j)^2*
          MixedPastNewestFiniteError.constant
            (ControlledSmoothLimit.roughTotalParameters D hh hh1 hcontract) κ M v b B Hr depth B0 A0 ν:=by
  let G:ℕ→Ω×HeatCircle→ℂ:=fun k z=>(Error k z:ℂ)
  let E:=MixedPastNewestFiniteError.field 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
    P haP v b hvb Z ht hs F hF hFm D j depth (fun _=>1)
  have hGm(k:ℕ):Measurable (G k):=Complex.continuous_ofReal.measurable.comp
    (MixedOrdinaryRootHilbertExpansion.error_measurable
      𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S J hIJ₀ hIJ₁ hnull hJ
      P hAs 0 v b hvb Z hrootStop hrootTarget F hF hFm hsmall hL k)
  have hGp(ω:Ω)(k:ℕ)(_hk:k∈Finset.range depth):
      MemLp (fun x=>G k (ω,x)) 2 AddCircle.haarAddCircle:=
    MixedOrdinaryRootHilbertExpansion.error_section_memLp
      𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S J hIJ₀ hIJ₁ hnull hJ
      P hAs 0 v b hvb Z hrootStop hrootTarget F hF hFm hsmall hL k ω
  have hscalar:=MixedPastNewestFiniteError.energy
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S J hIJ₀ hIJ₁ P haP v b hvb Z ht hs F hF hFm
    D hh hh1 hcontract j hP hB hHr hroot hrootmod hlocal (zero_le_one.trans hL)
    (MixedOrdinaryErrorPrimitive.ages b Z hrootStop hrootTarget)
    (MixedOrdinaryErrorPrimitive.stopUpper b Z hrootStop)
    (fun x i=>by simpa only [Subsingleton.elim i 0] using hrootTarget x)
    hspan hvb' hbH depth hold A0 ν hA hν hjet B0 hBDG (fun _=>1) (fun _ _=>by norm_num)
  have heq:∀ᵐz:Ω×HeatCircle∂μ.prod AddCircle.haarAddCircle,
      ‖∑k∈Finset.range depth,G k z‖^2=|E (z.2,z.1)|^2:=by
    filter_upwards [MixedOrdinaryErrorRootIdentity.canonical_finite_field_eq_ae
      𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S J hIJ₀ hIJ₁ hnull hJ
      P haP hAs v b hvb Z hrootStop hrootTarget F hF hFm hsmall hcoeff
      (zero_le_one.trans hL) D j hU hV depth (fun _=>1)] with z hz
    simp only [one_mul] at hz
    simp only [G,←Complex.ofReal_sum,Complex.norm_real,Real.norm_eq_abs,hz,E]
  have hsi:Integrable (fun z:Ω×HeatCircle=>‖∑k∈Finset.range depth,G k z‖^2)
      (μ.prod AddCircle.haarAddCircle):=hscalar.1.swap.congr (heq.mono (fun _ hz=>hz.symm))
  have hcap:(∫z:Ω×HeatCircle,‖∑k∈Finset.range depth,G k z‖^2 ∂μ.prod AddCircle.haarAddCircle)≤
      (ScalarApproximationDiscrepancy.scalarError D j)^2*
        MixedPastNewestFiniteError.constant
          (ControlledSmoothLimit.roughTotalParameters D hh hh1 hcontract) κ M v b B Hr depth B0 A0 ν:=by
    rw [integral_congr_ae heq]
    exact (integral_prod_swap (fun z:HeatCircle×Ω=>|E z|^2)).le.trans hscalar.2
  have hn:=NativeBesselFiniteSumEnergy.energy Λ ρ hL hρ μ (Finset.range depth) G hGm hGp hsi _ hcap
  simpa only [G,MixedOrdinaryRootHilbertExpansion.discrepancy,mul_assoc] using hn
end SHE.MixedOrdinaryFiniteHilbertError
