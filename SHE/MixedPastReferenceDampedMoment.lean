module

public import SHE.MixedPastReferencePartialField
public import SHE.MixedPastReferenceStopped
public import SHE.MixedPastReferenceField
public import SHE.MixedPastReferenceInput

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHE.MixedPastReferenceDampedMoment
open Set MeasureTheory PredictableL2 NativeHeatObservation NativeObservationNaturality
  FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation ControlledProfile
open MixedPastReference MixedPastReferenceStopped
open scoped NNReal ENNReal
local instance mixedPastReferenceDampedMoment_instance1 : Fact (0<2*Real.pi) := ⟨by positivity⟩
local instance mixedPastReferenceDampedMoment_instance2 : Fact ((2:ENNReal)≠⊤) := ⟨by simp⟩
local instance mixedPastReferenceDampedMoment_instance3 : MeasurableSpace RealL2 := borel _
local instance mixedPastReferenceDampedMoment_instance4 : BorelSpace RealL2 := ⟨rfl⟩
local instance mixedPastReferenceDampedMoment_instance5 : MeasurableSpace CircleL2 := borel _
local instance mixedPastReferenceDampedMoment_instance6 : BorelSpace CircleL2 := ⟨rfl⟩
local instance mixedPastReferenceDampedMoment_instance7 : MeasurableSpace RealHaarInput := borel _
local instance mixedPastReferenceDampedMoment_instance8 : BorelSpace RealHaarInput := ⟨rfl⟩
local instance mixedPastReferenceDampedMoment_instance9 : MeasurableSpace (Both RealHaarInput) := borel _
local instance mixedPastReferenceDampedMoment_instance10 : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
local instance mixedPastReferenceDampedMoment_instance11 : MeasurableSpace RealHaarIntegrand.Columns := borel _
local instance mixedPastReferenceDampedMoment_instance12 : BorelSpace RealHaarIntegrand.Columns := ⟨rfl⟩
variable {Ω : Type*} [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
variable (Λ κ : ℝ) (hκ : 0<κ) {aU aV : ℝ→ℝ} (haU : Measurable aU) (haV : Measurable aV) {ell M : ℝ}
variable (hell : 0<ell) (hbU : ∀ z,ell≤aU z ∧ aU z≤M) (hbV : ∀ z,ell≤aV z ∧ aV z≤M)
variable (I₀ I₁ : StandardTerminalIto (C:=RealHaarIntegrand.Columns) (E:=RealL2) 𝓕 μ H)
variable (u₀ : RealL2)
variable (S : MixedNativeAdditiveResidualPair.Solution 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀)

variable (J : StandardTerminalIto (C:=Both RealHaarInput) (E:=ℝ) 𝓕 μ H)
variable (hIJ₀ : StandardScalarNaturality I₀ (leftIntegral 𝓕 μ H J))
variable (hIJ₁ : StandardScalarNaturality I₁ (rightIntegral 𝓕 μ H J))

variable (P : CanonicalCovariance.ProfileParameters) (hΛ : 0≤Λ) (hκP : κ<P.lower)
variable (θ η : ℝ)
variable (hsmall : ProfileStability.memoryConstant P.lower P.holder P.exponent *
  ProfileVolterra.powerConstant ((P.exponent-1)/4)*P.horizon^(P.exponent/4)≤1/2)
variable (v b : ℝ≥0) (hvb : v<b) (hbH : b≤H) (hv1 : (v:ℝ)≤1)
variable (hsmallTime : (b:ℝ)-(v:ℝ)≤P.horizon)
variable (p : ℕ) (hp : 0<p) (Bpast : ℝ≥0)
variable (hBDGpast : StandardTerminalBDGPower (2*p) J Bpast)

variable (s : ℝ)

local notation "R" => input 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S J hIJ₀ hIJ₁
  P hΛ hκP θ η hsmall v b hvb hbH hv1 hsmallTime p hp Bpast hBDGpast s
local notation "span" => ((b:ℝ)-(v:ℝ))
local notation "D" => (fun ω => S.second v ω-S.first v ω)
local notation "Cref" => PastReferenceBracket.energyConstant P κ θ η span

include hIJ₀ hIJ₁ in
/-- Sharp conditional moments of the actual full-target partial
martingale. The deterministic gain exp(-Lambda*(b-v)) is retained,
alongside the genuine (b-v)^(beta/2) reference noise bracket gain. -/
theorem partial_moment_damped (hlocal : StandardTerminalPastLocality I₁)
    (Bnext : ℝ≥0) (hBDGnext : StandardTerminalBDGPower p I₁ Bnext)
    (A : Set Ω) (hA : MeasurableSet[𝓕 v] A) :
    let F := partialDifference 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S J hIJ₀ hIJ₁
      P hΛ hκP θ η hsmall v b hvb hbH hv1 hsmallTime p hp Bpast hBDGpast s
    Integrable (fun ω => ‖F ω‖^(2*p)) (μ.restrict A) ∧
      (∫ ω in A,‖F ω‖^(2*p) ∂μ)≤
        (2:ℝ)^(2*p-1)*((|θ-η| *Real.exp (-Λ*span))^(2*p)+(Bnext:ℝ)*Cref^p)*
          (∫ ω in A,‖D ω‖^(2*p) ∂μ) := by
  let Z : Ω→RealL2 := fun ω => ((θ-η)*Real.exp (-Λ*span)) • NativeHeatObservation.heat span (D ω)
  let N : Ω→RealL2 := I₁.integral R
  let F : Ω→RealL2 := fun ω => Z ω+N ω
  let K : ℝ := (2:ℝ)^(2*p-1)
  have hK : 0≤K := by positivity
  have hD := (data_moments 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S J hIJ₀ hIJ₁
    hΛ v (hvb.le.trans hbH) hv1 hp Bpast hBDGpast).2
  simp only [data,embed_norm] at hD
  have hDA := hD.integrableOn (s:=A)
  have hN := actual_moment 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S J hIJ₀ hIJ₁
    P hΛ hκP θ η hsmall v b hvb hbH hv1 hsmallTime p hp Bpast hBDGpast hlocal s Bnext hBDGnext A hA
  have hmD : Measurable D := MixedHeatedDifferenceMoments.difference_measurable
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S v
  have hmZ : StronglyMeasurable Z := by
    convert!
      (((NativeHeatObservation.heat span).continuous.measurable.comp hmD).stronglyMeasurable).const_smul
        ((θ-η)*Real.exp (-Λ*span)) using 1
  have hbZ (ω : Ω) : ‖Z ω‖^(2*p)≤(|θ-η| *Real.exp (-Λ*span))^(2*p)*‖D ω‖^(2*p) := by
    have hn : ‖Z ω‖≤(|θ-η| *Real.exp (-Λ*span))*‖D ω‖ := by
      dsimp only [Z]
      rw [norm_smul,Real.norm_eq_abs,abs_mul,abs_of_pos (Real.exp_pos _)]
      exact mul_le_mul_of_nonneg_left (RealHeat.realHeat_contraction _ _) (by positivity)
    simpa only [mul_pow] using pow_le_pow_left₀ (norm_nonneg _) hn (2*p)
  have hiZ : Integrable (fun ω => ‖Z ω‖^(2*p)) (μ.restrict A) :=
    (hDA.const_mul ((|θ-η| *Real.exp (-Λ*span))^(2*p))).mono' (hmZ.norm.pow _).aestronglyMeasurable.restrict
      (Filter.Eventually.of_forall (fun ω => by simpa only [Real.norm_of_nonneg (pow_nonneg (norm_nonneg _) _)] using hbZ ω))
  have hmF : AEStronglyMeasurable F (μ.restrict A) :=
    hmZ.aestronglyMeasurable.restrict.add
      (Lp.stronglyMeasurable (I₁.integral R)).aestronglyMeasurable.restrict
  have hbF (ω : Ω) : ‖F ω‖^(2*p)≤K*(‖Z ω‖^(2*p)+‖N ω‖^(2*p)) := by
    exact (pow_le_pow_left₀ (norm_nonneg _) (norm_add_le (Z ω) (N ω)) (2*p)).trans
      (add_pow_le (norm_nonneg _) (norm_nonneg _) (2*p))
  have hiMajor : Integrable (fun ω => K*(‖Z ω‖^(2*p)+‖N ω‖^(2*p))) (μ.restrict A) := by
    convert! (hiZ.add hN.1).const_mul K using 1
  have hiF : Integrable (fun ω => ‖F ω‖^(2*p)) (μ.restrict A) :=
    hiMajor.mono' (hmF.norm.pow _) (Filter.Eventually.of_forall (fun ω => by
      simpa only [Real.norm_of_nonneg (pow_nonneg (norm_nonneg _) _)] using hbF ω))
  change Integrable (fun ω => ‖F ω‖^(2*p)) (μ.restrict A) ∧ _
  refine ⟨hiF,?_⟩
  change (∫ ω in A,‖F ω‖^(2*p) ∂μ)≤_
  have hz := integral_mono hiZ (hDA.const_mul ((|θ-η| *Real.exp (-Λ*span))^(2*p))) hbZ
  rw [integral_const_mul] at hz
  calc
    _ ≤ ∫ ω in A,K*(‖Z ω‖^(2*p)+‖N ω‖^(2*p)) ∂μ := integral_mono hiF hiMajor hbF
    _ = K*((∫ ω in A,‖Z ω‖^(2*p) ∂μ)+(∫ ω in A,‖N ω‖^(2*p) ∂μ)) := by
      rw [integral_const_mul,integral_add hiZ hN.1]
    _ ≤ K*((|θ-η| *Real.exp (-Λ*span))^(2*p)*(∫ ω in A,‖D ω‖^(2*p) ∂μ)+
        (Bnext:ℝ)*Cref^p*(∫ ω in A,‖D ω‖^(2*p) ∂μ)) :=
      mul_le_mul_of_nonneg_left (add_le_add hz hN.2) hK
    _ = _ := by dsimp [K]; ring

end SHE.MixedPastReferenceDampedMoment
