module

public import SHE.ControlledFamilyMeanFields
public import SHE.ControlledFamilyKernelBounds
public import SHE.MixedHilbertKernelEnergy

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
set_option quotPrecheck false
noncomputable section

namespace SHE.ControlledFamilyMeanEnergy
open Set Filter MeasureTheory ProbabilityTheory Real PredictableL2 NativeHeatObservation
  NativeObservationNaturality FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation
  NativeRandomKernel ControlledProfile CutoffWordLevel CutoffWordHistories SmoothCylinders UniformSmooth
  ActualMeanKernel
open scoped NNReal ENNReal
local instance controlledFamilyMeanEnergy_period : Fact (0<2*π) := ⟨by positivity⟩
local instance controlledFamilyMeanEnergy_finiteExponent : Fact ((2:ENNReal)≠⊤) := ⟨by simp⟩
local instance controlledFamilyMeanEnergy_realSigma : MeasurableSpace RealL2 := borel _
local instance controlledFamilyMeanEnergy_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance controlledFamilyMeanEnergy_nativeSigma : MeasurableSpace CircleL2 := borel _
local instance controlledFamilyMeanEnergy_nativeBorel : BorelSpace CircleL2 := ⟨rfl⟩
local instance controlledFamilyMeanEnergy_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance controlledFamilyMeanEnergy_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance controlledFamilyMeanEnergy_blockSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance controlledFamilyMeanEnergy_blockBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
variable {Ω : Type} [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
variable (Λ κ : ℝ) (hκ : 0<κ) {aU aV : ℝ→ℝ} (haU : Measurable aU) (haV : Measurable aV) {ell M : ℝ}
variable (hell : 0<ell) (hbU : ∀ z,ell≤aU z ∧ aU z≤M) (hbV : ∀ z,ell≤aV z ∧ aV z≤M)
variable (I₀ I₁ : StandardTerminalIto (C:=RealHaarIntegrand.Columns) (E:=RealL2) 𝓕 μ H)
variable (u₀ : RealL2)
variable (S : MixedNativeAdditiveResidualPair.Solution 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀)
variable (J : StandardTerminalIto (C:=Both RealHaarInput) (E:=ℝ) 𝓕 μ H)
variable (hIJ₀ : StandardScalarNaturality I₀ (leftIntegral 𝓕 μ H J))
variable (hIJ₁ : StandardScalarNaturality I₁ (rightIntegral 𝓕 μ H J))
variable (P : CanonicalCovariance.ProfileParameters) (A : ℝ→ℝ) (hA : BoundedSmooth A)
variable (v b : ℝ≥0) (hvb : v≤b)
variable (Z : VariableObservations.Family HeatCircle 1)
variable (htarget : ∀ x i,(b:ℝ)≤(Z.observations x i).target)
variable (hstop : ∀ x i,(b:ℝ)≤(Z.observations x i).stop)
variable (F : HeatCircle→WordRecursion.State 1→ℝ) (hF : UniformBoundedSmooth F)
variable (hFm : Measurable (fun q : HeatCircle×WordRecursion.State 1=>F q.1 q.2))
local notation "Ref" => (fun a : ℝ×Inputs=>ControlledReferenceLevel.referenceData P A hA Λ a.1 v b hvb a.2)
local notation "Base" => ControlledReferenceThetaGeometry.level P A hA Λ v b hvb Z htarget hstop F hF hFm

include hIJ₀ hIJ₁ in
/-- The literal moving-reference mean mark tested against the ACTUAL
dependent common-driver current difference. Scalar Borel structure,
uniform coarse caps, exact right-heat factorization, current input
integrability and every global input moment are all derived here. Only
the sharp relative moment of the actual Gaussian word remains an input
to this analytic interface. -/
theorem actual_input_energy (hΛ : 0≤Λ) (q : ℝ≥0) (hqH : q≤H) (hq1 : (q:ℝ)≤1)
    (a : Ω→ℝ×Inputs) (ha : Measurable a) (k p : ℕ) (hp : 0<p)
    (m : Ω→History HeatCircle k→WordRecursion.State (1+k))
    (hm : Measurable (fun z : Ω×History HeatCircle k=>m z.1 z.2))
    (t : Fin k→ℝ) (r : ℝ) (hqr : (q:ℝ)≤r)
    (hr : ∀ a : ℝ×Inputs,r<fixedTerminal (R:=Ref a) (b:ℝ) k t)
    (B0 : ℝ≥0) (hBDG : StandardTerminalBDGPower ((2*p)*(k+2)) J B0)
    {mass ρ w amp χ CG : ℝ} (hmass : 1≤mass) (hρ : 0<ρ) (hρhalf : ρ<1/2)
    (hw : 0<w) (hw1 : w≤1) (hamp : 0≤amp) (hχ0 : 0≤χ) (hχ1 : χ<1)
    (hCG : 0≤CG) (horder : 1≤(p:ℝ)*(1-χ))
    (hMom : ∀ᵐ z : HeatCircle×HeatCircle ∂(AddCircle.haarAddCircle (T:=2*π)).prod AddCircle.haarAddCircle,
      (∫ ω,‖familyWeightedField Ref Base a k (fun _=>Λ) (fun _=>(q:ℝ)) (fun _=>r) m (fun _=>t) (ω,z)‖^(4*p) ∂μ)≤
        CG*(amp*‖ProfileVariance.heatPhysical (8*w) z.1 z.2‖)^(4*p)) :
    let V := fun ω=>S.second q ω-S.first q ω
    let I := familyMeanInput Ref Base a k mass ρ hmass hρ.le (fun _=>Λ) (fun _=>(q:ℝ)) m (fun _=>t) V
    let CD := MixedHeatedDifferenceMoments.momentConstant ((2*p)*(k+2)) B0 κ M^((1-χ)/(k+2:ℝ))
    let C := GaussianNegativePacket.constant ρ*(NativeHeatSpan.clock w)^(ρ-1/2)*amp^2*((CD+CG)/2)^(1/(p:ℝ))
    Integrable (fun ω=>‖I ω‖^2) μ ∧
      (∫ ω,‖I ω‖^2 ∂μ)≤C*(∫ ω,‖S.second q ω-S.first q ω‖^2 ∂μ)^χ := by
  intro V I CD C
  let G := familyWeightedField Ref Base a k (fun _=>Λ) (fun _=>(q:ℝ)) (fun _=>r) m (fun _=>t)
  let K := familyWeightedField Ref Base a k (fun _=>Λ) (fun _=>(q:ℝ)) (fun _=>(q:ℝ)) m (fun _=>t)
  have hG : Measurable G := ControlledFamilyMeanFields.familyWeightedField_measurable
    P A hA Λ v b hvb Z htarget hstop F hF hFm a ha k _ _ measurable_const measurable_const m hm _ measurable_const
  obtain ⟨B,hB,hbound⟩ := ControlledFamilyKernelBounds.weightedSpatial_family_uniform_bound
    P A hA Λ v b hvb Z htarget hstop F hF hFm k hΛ (q:ℝ) r t
  have hc : ∀ ω y x,‖G (ω,(y,x))‖≤B := fun ω y x=>hbound (a ω) (m ω) y x
  have hm' : ∀ ω,Measurable (m ω) := fun ω=>hm.comp (measurable_const.prodMk measurable_id)
  have hsplit (ω : Ω) : integralOperator K ω (embed (V ω))=
      integralOperator G ω (HeatedCurrentInput.value (r-(q:ℝ)) V ω) :=
    family_weighted_input_split Ref Base a k (fun _=>Λ) (fun _=>(q:ℝ)) (fun _=>r) (fun _=>(b:ℝ))
      (fun _ _=>rfl) (fun _=>hΛ) m hm' (fun _=>t) (fun _=>hqr) (fun ω=>hr (a ω)) V ω
  exact MixedHilbertKernelEnergy.actual_input_energy 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
    J hIJ₀ hIJ₁ hΛ q hqH hq1 k p hp B0 hBDG K G hG hB hc (r-q) (sub_nonneg.mpr hqr)
    hmass hρ hρhalf hw hw1 hamp hχ0 hχ1 hCG horder hMom hsplit

end SHE.ControlledFamilyMeanEnergy
