module
public import SHE.MixedOrdinaryRootFields
public import SHE.NativeBesselFiniteIdentity
public import SHE.MixedOrdinaryNoiseHilbert
public import SHE.OrdinaryUncutSampleExpansion
public import SHE.ControlledReferenceFamilyEvaluation
public import SHE.MixedOrdinaryWeightedPhysicalCoordinates
public import SHE.NativeBesselFieldAE
public import SHE.PastParameterDiagonal

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
set_option quotPrecheck false
namespace SHE.MixedOrdinaryRootHilbertExpansion
open Set MeasureTheory PredictableL2 StoppedFourier WordRecursion ControlledProfile ControlledReferenceLevel
  CutoffWordLevel CutoffWordHistories SmoothCylinders UniformSmooth OrthogonalItoChannels FiniteHaar DyadicApproximation
  NativeHeatObservation NativeObservationNaturality
open scoped NNReal ENNReal
local instance mixedOrdinaryPhysicalCoordinates_period:Fact (0<2*Real.pi):=⟨by positivity⟩
local instance mixedOrdinaryPhysicalCoordinates_sigma:MeasurableSpace CircleL2:=borel _
local instance mixedOrdinaryPhysicalCoordinates_borel:BorelSpace CircleL2:=⟨rfl⟩
local instance mixedOrdinaryNoiseHilbert_second:SecondCountableTopology CircleL2:=
  (_root_.fourierBasis (T:=2*Real.pi)).repr.toHomeomorph.secondCountableTopology
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


local notation "Field"=>MixedOrdinaryRootFields.field 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S J hIJ₀ hIJ₁ hnull hJ P hAs θ v b hvb Z hstop htarget F hF hFm
local notation "Error"=>MixedOrdinaryRootFields.error 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S J hIJ₀ hIJ₁ hnull hJ P hAs θ v b hvb Z hstop htarget F hF hFm
local notation "NF"=>MixedOrdinaryWeightedPhysicalCoordinates.noiseField 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S J hIJ₀ hIJ₁ hnull hJ P hAs θ v b hvb Z hstop htarget F hF hFm
variable (hL:1≤Λ){ρ:ℝ}(hρ:0≤ρ)

def term(i:Fin 2)(k:ℕ)(ω:Ω):CircleL2:=
  NativeBesselFieldAE.value Λ ρ hL hρ (fun z:Ω×HeatCircle=>(Field i k z:ℂ)) ω
local notation "Term"=>term 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S J hIJ₀ hIJ₁ hnull hJ P hAs θ v b hvb Z hstop htarget F hF hFm hL hρ

def discrepancy(k:ℕ)(ω:Ω):CircleL2:=
  NativeBesselFieldAE.value Λ ρ hL hρ (fun z:Ω×HeatCircle=>(Error k z:ℂ)) ω
local notation "Discrepancy"=>discrepancy 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S J hIJ₀ hIJ₁ hnull hJ P hAs θ v b hvb Z hstop htarget F hF hFm hL hρ
local notation "Noise"=>MixedOrdinaryNoiseHilbert.value 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S J hIJ₀ hIJ₁ hnull hJ P hAs θ v b hvb Z hstop htarget F hF hFm hL hρ

include hsmall hL in
theorem error_measurable(k:ℕ):Measurable (Error k):=by
  have hf:=MixedOrdinaryRootFields.field_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S J hIJ₀ hIJ₁ hnull hJ P hAs θ v b hvb Z hstop htarget F hF hFm hsmall (zero_le_one.trans hL)
  have hn:=MixedOrdinaryNoiseHilbert.field_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S J hIJ₀ hIJ₁ hnull hJ P hAs θ v b hvb Z hstop htarget F hF hFm hsmall (zero_le_one.trans hL)
  exact (((hf 0 k).sub (hf 1 k)).sub (hn k)).sub (hf 0 (k+1))

include hsmall hL in
theorem error_section_memLp(k:ℕ)(ω:Ω):
    MemLp (fun x:HeatCircle=>(Error k (ω,x):ℂ)) 2 AddCircle.haarAddCircle:=by
  have hf:=MixedOrdinaryRootFields.section_memLp 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S J hIJ₀ hIJ₁ hnull hJ P hAs θ v b hvb Z hstop htarget F hF hFm hsmall (zero_le_one.trans hL)
  have hn:=MixedOrdinaryNoiseHilbert.section_memLp 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S J hIJ₀ hIJ₁ hnull hJ P hAs θ v b hvb Z hstop htarget F hF hFm hsmall (zero_le_one.trans hL) k ω
  have hparts:=(((hf 0 k ω).sub (hf 1 k ω)).sub hn).sub (hf 0 (k+1) ω)
  convert hparts using 1
  ext x
  simp only [MixedOrdinaryRootFields.error,Complex.ofReal_sub,Pi.sub_apply]

include hsmall in
theorem term_measurable(i:Fin 2)(k:ℕ):Measurable (Term i k):=
  NativeBesselFieldAE.measurable Λ ρ hL hρ _ (Complex.continuous_ofReal.measurable.comp
    (MixedOrdinaryRootFields.field_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S J hIJ₀ hIJ₁ hnull hJ P hAs θ v b hvb Z hstop htarget F hF hFm hsmall (zero_le_one.trans hL) i k))

include hsmall in
theorem discrepancy_measurable(k:ℕ):Measurable (Discrepancy k):=
  NativeBesselFieldAE.measurable Λ ρ hL hρ _ (Complex.continuous_ofReal.measurable.comp
    (error_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S J hIJ₀ hIJ₁ hnull hJ P hAs θ v b hvb Z hstop htarget F hF hFm hsmall hL k))

include hsmall in
/-- Exact ordinary native recursion. The discrepancy is the native image
of the genuine rough-minus-smooth bracket error, with its positive sign. -/
theorem cycle(k:ℕ)(ω:Ω):
    Term 0 k ω=Term 1 k ω+Noise k ω+Discrepancy k ω+Term 0 (k+1) ω:=by
  let G:Fin 4→Ω×HeatCircle→ℂ:=fun i=>
    if i=0 then (fun z=>(Field 1 k z:ℂ))
    else if i=1 then (fun z=>(NF k z:ℂ))
    else if i=2 then (fun z=>(Error k z:ℂ))
    else (fun z=>(Field 0 (k+1) z:ℂ))
  have hf:=MixedOrdinaryRootFields.field_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S J hIJ₀ hIJ₁ hnull hJ P hAs θ v b hvb Z hstop htarget F hF hFm hsmall (zero_le_one.trans hL)
  have hn:=MixedOrdinaryNoiseHilbert.field_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S J hIJ₀ hIJ₁ hnull hJ P hAs θ v b hvb Z hstop htarget F hF hFm hsmall (zero_le_one.trans hL)
  have he:=error_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S J hIJ₀ hIJ₁ hnull hJ P hAs θ v b hvb Z hstop htarget F hF hFm hsmall hL k
  have hm(i:Fin 4):Measurable (G i):=by
    fin_cases i
    · exact Complex.continuous_ofReal.measurable.comp (hf 1 k)
    · exact Complex.continuous_ofReal.measurable.comp (hn k)
    · exact Complex.continuous_ofReal.measurable.comp he
    · exact Complex.continuous_ofReal.measurable.comp (hf 0 (k+1))
  have hp:=MixedOrdinaryRootFields.section_memLp 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S J hIJ₀ hIJ₁ hnull hJ P hAs θ v b hvb Z hstop htarget F hF hFm hsmall (zero_le_one.trans hL)
  have hgp(i:Fin 4):MemLp (fun x=>G i (ω,x)) 2 AddCircle.haarAddCircle:=by
    fin_cases i
    · exact hp 1 k ω
    · exact MixedOrdinaryNoiseHilbert.section_memLp 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S J hIJ₀ hIJ₁ hnull hJ P hAs θ v b hvb Z hstop htarget F hF hFm hsmall (zero_le_one.trans hL) k ω
    · exact error_section_memLp 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S J hIJ₀ hIJ₁ hnull hJ P hAs θ v b hvb Z hstop htarget F hF hFm hsmall hL k ω
    · exact hp 0 (k+1) ω
  have hid:∀ᵐx∂AddCircle.haarAddCircle,(Field 0 k (ω,x):ℂ)=∑i:Fin 4,G i (ω,x):=by
    apply ae_of_all
    intro x
    simp [Fin.sum_univ_succ,G,Fin.succ,Fin.mk.injEq,
      MixedOrdinaryRootFields.error,Complex.ofReal_sub]
  have hall:=NativeBesselFiniteIdentity.finite_sum Λ ρ hL hρ Finset.univ
    (fun z:Ω×HeatCircle=>(Field 0 k z:ℂ)) (Complex.continuous_ofReal.measurable.comp (hf 0 k))
    G hm ω (hp 0 k ω) (fun i _=>hgp i) hid
  simpa [term,discrepancy,MixedOrdinaryNoiseHilbert.value,Fin.sum_univ_succ,G,Fin.succ,
    Fin.mk.injEq,add_assoc] using hall

include hsmall in
/-- Finite-depth expansion of the genuine ordinary U, retaining every
positive rough-minus-smooth error before subtraction from the joint expansion. -/
theorem finite_expansion(depth:ℕ)(ω:Ω):
    Term 0 0 ω=(∑k∈Finset.range depth,Term 1 k ω)+
      (∑k∈Finset.range depth,Noise k ω)+(∑k∈Finset.range depth,Discrepancy k ω)+Term 0 depth ω:=by
  induction depth with
  | zero=>simp
  | succ d ih=>
    have hc:=cycle 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S J hIJ₀ hIJ₁ hnull hJ P hAs θ v b hvb Z hstop htarget F hF hFm hsmall hL hρ d ω
    simp only [Finset.sum_range_succ]
    rw [hc] at ih
    abel_nf at ih ⊢
    exact ih
end SHE.MixedOrdinaryRootHilbertExpansion
