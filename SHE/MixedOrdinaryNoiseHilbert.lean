module
public import SHE.MixedOrdinaryWeightedPhysicalCoordinates
public import SHE.NativeBesselFieldAE
public import SHE.PastParameterDiagonal

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
set_option quotPrecheck false
namespace SHE.MixedOrdinaryNoiseHilbert
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

local notation "Noise"=>(fun k (z:Ω×History HeatCircle k)=>
  OrdinaryUncutNoise.value modelU (Base (pastParameter z.1)) k z.2 z.1)
local notation "NF"=>MixedOrdinaryWeightedPhysicalCoordinates.noiseField
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S J hIJ₀ hIJ₁ hnull hJ
  P hAs θ v b hvb Z hstop htarget F hF hFm

include hsmall in
theorem raw_measurable(hΛ:0≤Λ)(k:ℕ):Measurable (Noise k):=by
  have hu:StronglyMeasurable pastParameter:=
    (MixedNativeRandomReferenceStep.randomParameter_stronglyMeasurable
      𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S v).mono (𝓕.le v)
  have huQ:StronglyMeasurable (fun z:Ω×History HeatCircle k=>pastParameter z.1):=
    hu.comp_measurable measurable_fst
  have hm(p:Inputs):Measurable (fun z:Ω×History HeatCircle k=>
      OrdinaryUncutNoise.value modelU (Base p) k z.2 z.1):=
    (OrdinaryUncutNoise.value_measurable modelU (Base p) k).comp measurable_swap
  exact (PastParameterDiagonal.stronglyMeasurable_diagonal
    (inferInstance:MeasurableSpace (Ω×History HeatCircle k)) le_rfl
    (fun p z=>OrdinaryUncutNoise.value modelU (Base p) k z.2 z.1) hm huQ
    (fun z=>ControlledOrdinaryNoise.value_continuous P (fun z=>κ+aV z) hAs Λ θ v b hvb
      Z ht hs F hF hFm modelU hsmall hΛ k z.2 z.1)).measurable

include hsmall in
theorem field_measurable(hΛ:0≤Λ)(k:ℕ):Measurable (NF k):=
  RootSectionAverage.measurable R₀ k (Noise k)
    (raw_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S J hIJ₀ hIJ₁ hnull hJ
      P hAs θ v b hvb Z hstop htarget F hF hFm hsmall hΛ k)

include hsmall in
theorem field_bound(hΛ:0≤Λ)(k:ℕ):∃C:ℝ,0≤C∧∀z,‖NF k z‖≤C:=by
  obtain ⟨C,hC,hCb⟩:=ControlledOrdinaryNoise.value_bound P (fun z=>κ+aV z) hAs Λ θ v b hvb
    Z ht hs F hF hFm modelU k
  refine ⟨C*UncutHistoryMass.massBound (R:=R₀) (n:=1) (AddCircle.haarAddCircle:Measure HeatCircle) k,
    mul_nonneg hC (UncutHistoryMass.massBound_nonneg _ k),?_⟩
  intro z
  exact RootSectionAverage.norm_le (Base (0,0)) k (Noise k)
    (raw_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S J hIJ₀ hIJ₁ hnull hJ
      P hAs θ v b hvb Z hstop htarget F hF hFm hsmall hΛ k)
    C hC (fun ω h=>hCb (pastParameter ω) h ω) z.1 z.2

include hsmall in
theorem section_memLp(hΛ:0≤Λ)(k:ℕ)(ω:Ω):
    MemLp (fun x:HeatCircle=>(NF k (ω,x):ℂ)) 2 AddCircle.haarAddCircle:=by
  obtain ⟨C,hC,hCb⟩:=field_bound
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S J hIJ₀ hIJ₁ hnull hJ
    P hAs θ v b hvb Z hstop htarget F hF hFm hsmall hΛ k
  apply MemLp.of_bound
    ((Complex.continuous_ofReal.measurable.comp (field_measurable
      𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S J hIJ₀ hIJ₁ hnull hJ
      P hAs θ v b hvb Z hstop htarget F hF hFm hsmall hΛ k)).comp
        (measurable_const.prodMk measurable_id)).aestronglyMeasurable C
  filter_upwards with x
  change ‖(NF k (ω,x):ℂ)‖≤C
  simpa only [Complex.norm_real] using hCb (ω,x)

variable (hL:1≤Λ){ρ:ℝ}(hρ:0≤ρ)
def value(k:ℕ)(ω:Ω):CircleL2:=
  NativeBesselFieldAE.value Λ ρ hL hρ (fun z:Ω×HeatCircle=>(NF k z:ℂ)) ω
local notation "Value"=>value
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S J hIJ₀ hIJ₁ hnull hJ
  P hAs θ v b hvb Z hstop htarget F hF hFm hL hρ

include hsmall in
theorem measurable(k:ℕ):Measurable (Value k):=
  NativeBesselFieldAE.measurable Λ ρ hL hρ _
    (Complex.continuous_ofReal.measurable.comp (field_measurable
      𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S J hIJ₀ hIJ₁ hnull hJ
      P hAs θ v b hvb Z hstop htarget F hF hFm hsmall (zero_le_one.trans hL) k))

include hsmall in
theorem coefficients(k:ℕ)(ω:Ω)(l:ℤ):
    fourierCoeff (Value k ω) l=
      (((Λ+(l:ℝ)^2)^(-ρ/2):ℝ):ℂ)*fourierCoeff (fun x:HeatCircle=>(NF k (ω,x):ℂ)) l:=by
  have hm:=Complex.continuous_ofReal.measurable.comp (field_measurable
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S J hIJ₀ hIJ₁ hnull hJ
    P hAs θ v b hvb Z hstop htarget F hF hFm hsmall (zero_le_one.trans hL) k)
  exact NativeBesselFieldAE.coefficients Λ ρ hL hρ _ hm ω
    ((MeasurableL2FieldAE.section_memLp_iff AddCircle.haarAddCircle _ hm ω).mp
      (section_memLp 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S J hIJ₀ hIJ₁ hnull hJ
        P hAs θ v b hvb Z hstop htarget F hF hFm hsmall (zero_le_one.trans hL) k ω)) l

include hIJ₀ hIJ₁ hnull hJ hstop htarget hcenter hsmall in
/-- Every real Fourier coordinate of the actual ordinary-U native
Bessel field is the SAME original-J input with its full raw identity. -/
theorem original_input_fourier(hlocal:StandardTerminalPastLocality J)(hbH:b≤H)(hb1:(b:ℝ)≤1)
    (hvb':v<b)(a:ℂ→L[ℝ]ℝ)(l:ℤ)(k:ℕ):
    ∃input:Process (E:=Both RealHaarInput) 𝓕 μ H,
      J.integral input=ᵐ[μ] (fun ω=>a (fourierCoeff (Value k ω) l))∧
      ∀ᵐz∂energyMeasure μ H,∀ℓ:Both RealHaarInput→L[ℝ]ℝ,
        ℓ (input z)=∫x:HeatCircle,NativeScalarFourierWeight.value ((Λ+(l:ℝ)^2)^(-ρ/2)) a l x*
          MixedOrdinaryWeightedPhysicalCoordinates.coordinateField
            𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S J hIJ₀ hIJ₁ hnull hJ
            P hAs θ v b hvb Z hstop htarget F hF hFm k ℓ (z,x) ∂AddCircle.haarAddCircle:=by
  obtain ⟨input,hout,hcoord⟩:=MixedOrdinaryWeightedPhysicalCoordinates.original_input_fourier
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S J hIJ₀ hIJ₁ hnull hJ
    P hAs θ v b hvb Z hstop htarget hcenter F hF hFm hsmall hlocal (zero_le_one.trans hL)
    hbH hb1 hvb' ((Λ+(l:ℝ)^2)^(-ρ/2)) a l k
  refine ⟨input,hout.trans (ae_of_all _ (fun ω=>?_)),hcoord⟩
  change (Λ+(l:ℝ)^2)^(-ρ/2)*a (fourierCoeff (fun x:HeatCircle=>(NF k (ω,x):ℂ)) l)=
    a (fourierCoeff (Value k ω) l)
  rw [coefficients 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S J hIJ₀ hIJ₁ hnull hJ
    P hAs θ v b hvb Z hstop htarget F hF hFm hsmall hL hρ k ω l]
  change _=a (((Λ+(l:ℝ)^2)^(-ρ/2)) • fourierCoeff (fun x:HeatCircle=>(NF k (ω,x):ℂ)) l)
  rw [map_smul,smul_eq_mul]

end SHE.MixedOrdinaryNoiseHilbert

