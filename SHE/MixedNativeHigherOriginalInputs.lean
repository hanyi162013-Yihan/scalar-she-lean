module
public import SHE.MixedNativeHigherOriginalEnergy
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
namespace SHE.MixedNativeHigherOriginalInputs
open Set MeasureTheory PredictableL2 StoppedFourier WordRecursion ControlledProfile ControlledReferenceLevel
  CutoffWordLevel CutoffWordHistories SmoothCylinders UniformSmooth OrthogonalItoChannels FiniteHaar DyadicApproximation
  NativeHeatObservation NativeObservationNaturality
open scoped NNReal ENNReal
local instance mixedNativeHigherOriginalInputs_period:Fact (0<2*Real.pi):=⟨by positivity⟩
local instance mixedNativeHigherOriginalInputs_sigma:MeasurableSpace CircleL2:=borel _
local instance mixedNativeHigherOriginalInputs_borel:BorelSpace CircleL2:=⟨rfl⟩
local instance mixedNativeHigherOriginalInputs_realSigma:MeasurableSpace RealL2:=borel _
local instance mixedNativeHigherOriginalInputs_realBorel:BorelSpace RealL2:=⟨rfl⟩
local instance mixedNativeHigherOriginalInputs_rowSigma:MeasurableSpace RealHaarInput:=borel _
local instance mixedNativeHigherOriginalInputs_rowBorel:BorelSpace RealHaarInput:=⟨rfl⟩
local instance mixedNativeHigherOriginalInputs_blockSigma:MeasurableSpace (Both RealHaarInput):=borel _
local instance mixedNativeHigherOriginalInputs_blockBorel:BorelSpace (Both RealHaarInput):=⟨rfl⟩
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
local notation "C1"=>MixedCanonicalWeightedPhysicalCoordinates.coordinate
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S P hAs 1 v b hvb Z ht hs F hF hFm
local notation "C0"=>(fun k (ℓ:Both RealHaarInput→L[ℝ]ℝ) (z:(ℝ≥0×Ω)×History HeatCircle k)=>
  OrdinaryPhysicalCoordinates.coordinate modelU (Base0 (pastParameter z.1.2)) k ℓ (z.2,z.1))
local notation "Raw"=>MixedNativeColumnRawFourier.raw
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S J hIJ₀ hIJ₁ hnull hJ
  P haP v b hvb Z ht hs F hF hFm
local notation "JointValue"=>MixedCanonicalNoiseIncrement.value
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S P hAs 1 v b hvb Z ht hs F hF hFm
local notation "OrdinaryValue"=>MixedOrdinaryNoiseHilbert.value
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S J hIJ₀ hIJ₁ hnull hJ
  P hAs 0 v b hvb Z hrootStop hrootTarget F hF hFm

local notation "Value"=>MixedNativeHigherOriginalEnergy.value 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S J hIJ₀ hIJ₁ hnull hJ
  P hAs v b hvb Z hrootStop hrootTarget F hF hFm
local notation "Source0"=>MixedNativeOriginalFourierRows.left
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP v b hvb Z ht hs F hF hFm
local notation "Source1"=>MixedNativeOriginalFourierRows.right
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP v b hvb Z ht hs F hF hFm
local notation "Add"=>MixedPastNativeOldTimeEnergy.additive
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP v b hvb Z ht hs F hF hFm
local notation "BaseCols"=>MixedPastNativeOldTimeEnergy.base
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP v b hvb Z ht hs F hF hFm
local notation "Signed"=>MixedPastSignedEndpointFields.raw
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP v b hvb Z ht hs F hF hFm
attribute [local irreducible] MixedNativeHigherOriginalEnergy.value MixedNativeOriginalFourierRows.left MixedNativeOriginalFourierRows.right

variable (hsmall:ProfileStability.memoryConstant P.lower P.holder P.exponent*
  ProfileVolterra.powerConstant ((P.exponent-2)/4)*P.horizon^(P.exponent/4)≤1/2)

include hIJ₀ hIJ₁ hnull hJ hrootStop hrootTarget hcenter hsmall in
/-- The actual paired native output has SAME-original-J Fourier inputs
with the literal complete guarded columns, on one current/sample event.
Every random-past, cutoff and raw-coordinate applicability is derived. -/
theorem inputs(hA:P.coefficient=(fun z=>κ+aV z))
    (hlocal:StandardTerminalPastLocality J)(hL:1≤Λ){ρ:ℝ}(hρ:0<ρ)(hρhalf:ρ<1/2)
    (hbH:b≤H)(hb1:(b:ℝ)≤1)(hvb':v<b)(k:ℕ)
    (hsmallL2:ProfileStability.memoryConstant P.lower P.holder P.exponent*
      ProfileVolterra.powerConstant ((P.exponent-1)/4)*P.horizon^(P.exponent/4)≤1/2)
    (hspan:(b:ℝ)-(v:ℝ)≤P.horizon)
    (hspanF:(b:ℝ)-(v:ℝ)≤NativeUniversalConstants.rowHorizon (1+k))
    (hspanC:(b:ℝ)-(v:ℝ)≤4*Real.pi^2*NativeUniversalConstants.currentHorizon.{0} (1+k) (by omega))
    (hspanS:(b:ℝ)-(v:ℝ)≤UniformFutureProfileScores.horizon (1+k))
    (hHistory:∀j,j<k→(b:ℝ)-(v:ℝ)≤PhysicalScoreChain.uniformHorizon 1 j)
    (B1:ℝ≥0)(hBDG1:StandardTerminalBDGPower 1 J B1)
    (A0 ν:ℝ)(hA0:0≤A0)(hν:0≤ν)
    (hjet:∀x j,j≤k→∀z,‖iteratedFDeriv ℝ j (F x) z‖≤A0*ν^j)
    (p:ℕ)(hp:0<p)(Bcur:ℝ≥0)(hBDGcur:StandardTerminalBDGPower (p*(k+2)) J Bcur)
    (Bword:ℝ≥0)(hBDGword:StandardTerminalBDGPower (k+2) J Bword)
    (χ:ℝ)(hχ:0≤χ)(hχ1:χ<1)(horder:1≤(p:ℝ)*(1-χ))
    (lam ε tail η:ℝ)(hlam:1≤lam)(htail:tail≤ε*(2*((p-1:ℕ):ℝ)))(hη:0<η)(hρη:ρ+η<1):
    ∀(a:ℂ→L[ℝ]ℝ)(l:ℤ),∃input:Process (E:=Both RealHaarInput) 𝓕 μ H,
      J.integral input=ᵐ[μ] (fun ω=>a (fourierCoeff (Value hL hρ.le k ω) l)) ∧
      input=ᵐ[energyMeasure μ H] fun z=>WithLp.toLp 2
        (HilbertColumns.mapCLM (a.comp (NativeFourierNoiseRows.coefficient l)) (Source0 k hL hρ.le z),
         HilbertColumns.mapCLM (a.comp (NativeFourierNoiseRows.coefficient l)) (Source1 k hL hρ.le z)):=by
  have hΛ:0<Λ:=zero_lt_one.trans_le hL
  have htarget':∀x i,(Z.observations x i).target=(b:ℝ):=by
    intro x i
    simpa only [Subsingleton.elim i 0] using hrootTarget x
  have hstop':∀x i,(Z.observations x i).stop=(b:ℝ):=by
    intro x i
    simpa only [Subsingleton.elim i 0] using hrootStop x
  have hcenter':∀x i,(Z.observations x i).center=x:=by
    intro x i
    simpa only [Subsingleton.elim i 0] using hcenter x
  have hSections(q:ℝ≥0)(hvq:v<q)(hqb:q<b):∀ᵐω∂μ,
      Integrable (fun t=>Add k q hL hρ.le (t,ω))
        (Measure.pi (fun _:Fin k=>volume.restrict (Ioc (v:ℝ) (b:ℝ))))∧
      Integrable (fun t=>BaseCols k q hL hρ.le (t,ω))
        (Measure.pi (fun _:Fin k=>volume.restrict (Ioc (v:ℝ) (b:ℝ))))∧
      Integrable (fun t=>Signed k q hL hρ.le (t,ω))
        (Measure.pi (fun _:Fin k=>volume.restrict (Ioc (v:ℝ) (b:ℝ)))):=by
    have hqH:q≤H:=hqb.le.trans hbH
    have hqbR:(q:ℝ)≤(b:ℝ):=by exact_mod_cast hqb.le
    have hq1:(q:ℝ)≤1:=hqbR.trans hb1
    have hw1:(b:ℝ)-(q:ℝ)≤1:=by linarith [q.property]
    have hsec:=MixedPastNativeCompleteSections.integrable
      𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S J hIJ₀ hIJ₁
      P haP v b hvb Z ht hs F hF hFm k hΛ hlocal hsmall hsmallL2 htarget' hstop' hcenter'
      hspan hspanF hspanC hspanS hHistory q hvq hqb hqH hq1 hw1
      B1 hBDG1 A0 ν hA0 hν hjet p hp Bcur hBDGcur Bword hBDGword χ hχ hχ1 horder
      Λ ρ lam ε tail η hL hρ hρhalf hlam htail hη hρη
    filter_upwards [hsec.1.prod_left_ae,hsec.2.1.prod_left_ae,hsec.2.2.prod_left_ae] with ω h0 hU hD
    exact ⟨h0,hU,hD⟩
  have hex(a:ℂ→L[ℝ]ℝ)(l:ℤ):∃input:Process (E:=Both RealHaarInput) 𝓕 μ H,
      J.integral input=ᵐ[μ] (fun ω=>a (fourierCoeff (Value hL hρ.le k ω) l)) ∧
      input=ᵐ[energyMeasure μ H] fun z=>WithLp.toLp 2
        (HilbertColumns.mapCLM (a.comp (NativeFourierNoiseRows.coefficient l)) (Source0 k hL hρ.le z),
         HilbertColumns.mapCLM (a.comp (NativeFourierNoiseRows.coefficient l)) (Source1 k hL hρ.le z)):=by
    obtain ⟨input,hout,hraw⟩:=MixedNativePairedOriginalInput.original_input_fourier
      𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S J hIJ₀ hIJ₁ hnull hJ
      P haP hAs v b hvb Z hrootStop hrootTarget hcenter F hF hFm hsmall
      hA hlocal hL hρ.le hbH hb1 hvb' a l k
    refine ⟨input,?_,?_⟩
    · simpa only [MixedNativeHigherOriginalEnergy.value] using hout
    apply MixedNativeOriginalFourierRows.input_ae
      𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S J hIJ₀ hIJ₁ hnull hJ
      P haP v b hvb Z ht hs F hF hFm hΛ.le
      (fun x i=>by rw [hstop' x i,htarget' x i]) (fun x i=>(hstop' x i).le)
      k hL hρ.le hSections
      (hraw.mono (fun z hz ℓ=>(hz ℓ).1)) l a input
    exact hraw.mono (fun z hz ℓ=>(hz ℓ).2)
  exact hex

end SHE.MixedNativeHigherOriginalInputs
