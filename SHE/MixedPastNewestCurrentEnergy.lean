module
public import SHE.MixedPastNewestAverage
public import SHE.PastNewestCurrentMass
public import SHE.SectionEnergy
public import SHE.PastNewestOldTimeEnergy
public import SHE.MixedPastNewestFields
public import SHE.ParentScoreInput
public import SHE.ParentMeanMass
public import SHE.WeightedSFiniteMoments
public import SHE.PastWordTimeFields

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 2600000
namespace SHE.MixedPastNewestCurrentEnergy
open Set MeasureTheory ProbabilityTheory Real AddCircle PredictableL2 NativeHeatObservation NativeObservationNaturality
  FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation StoppedItoInputs
  GaussianIncrement ControlledOldIntervals MeasurableGaussianScores PhysicalProfile
  WordRecursion CutoffWordLevel CutoffWordHistories CutoffCarriers PhysicalScoreChain PhysicalChainArrays
  PhysicalParentGeometry ControlledProfile ControlledReferenceLevel ControlledReferenceWindows
  ControlledFamilyProfileForest CoveredHistoryGeometry CoveredControlledLaw SmoothCylinders UniformSmooth GaussianConvolution
open scoped NNReal ENNReal BigOperators
local instance mixedPastNewestCurrentEnergy_realSigma : MeasurableSpace RealL2:=borel _
local instance mixedPastNewestCurrentEnergy_realBorel : BorelSpace RealL2:=⟨rfl⟩
local instance mixedPastNewestCurrentEnergy_rowSigma : MeasurableSpace RealHaarInput:=borel _
local instance mixedPastNewestCurrentEnergy_rowBorel : BorelSpace RealHaarInput:=⟨rfl⟩
local instance mixedPastNewestCurrentEnergy_bothSigma : MeasurableSpace (Both RealHaarInput):=borel _
local instance mixedPastNewestCurrentEnergy_bothBorel : BorelSpace (Both RealHaarInput):=⟨rfl⟩
local instance mixedPastNewestCurrentEnergy_circleSigma : MeasurableSpace CircleL2:=borel _
local instance mixedPastNewestCurrentEnergy_circleBorel : BorelSpace CircleL2:=⟨rfl⟩
local instance mixedPastNewestCurrentEnergy_period : Fact (0<2*π):=⟨by positivity⟩
attribute [local irreducible] MixedPastNewestError.value WordRecursion.directionalSecond
  GaussianConvolution.gaussianAverage UncutSmoothWords.test MeasurableGaussianScores.scoreVariance
  MeasurableGaussianScores.coefficient MeasurableGeneralizedInverse.generalizedInverse
variable {Ω:Type}[MeasurableSpace Ω]{X:Type}[MeasurableSpace X]
variable (𝓕:Filtration ℝ≥0 ‹MeasurableSpace Ω›)(μ:Measure Ω)[IsProbabilityMeasure μ](H:ℝ≥0)
variable (Λ κ:ℝ)(hκ:0<κ){aU aV:ℝ→ℝ}(haU:Measurable aU)(haV:Measurable aV){ell M:ℝ}
variable (hell:0<ell)(hbU:∀z,ell≤aU z ∧ aU z≤M)(hbV:∀z,ell≤aV z ∧ aV z≤M)
variable (I₀ I₁:StandardTerminalIto (C:=RealHaarIntegrand.Columns) (E:=RealL2) 𝓕 μ H)
variable (u₀ v₀:RealL2)
variable (S:MixedNativeAdditiveResidualPair.Solution 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀)
variable (J:StandardTerminalIto (C:=Both RealHaarInput) (E:=ℝ) 𝓕 μ H)
variable (hIJ₀:StandardScalarNaturality I₀ (leftIntegral 𝓕 μ H J))
variable (hIJ₁:StandardScalarNaturality I₁ (rightIntegral 𝓕 μ H J))
variable (P:CanonicalCovariance.ProfileParameters)(haP:BoundedSmooth P.coefficient)
variable (v b:ℝ≥0)(hvb:v≤b)(Z:VariableObservations.Family X 1)
variable (htarget:∀x i,(b:ℝ)≤(Z.observations x i).target)
variable (hstop:∀x i,(b:ℝ)≤(Z.observations x i).stop)
variable (F:X→WordRecursion.State 1→ℝ)(hF:UniformBoundedSmooth F)
variable (hFm:Measurable (fun z:X×WordRecursion.State 1=>F z.1 z.2))
local notation "Base"=>ControlledReferenceThetaGeometry.level P P.coefficient haP Λ v b hvb Z htarget hstop F hF hFm
local notation "Zero"=>Base (0,(0,0))
local notation "Value"=>MixedPastNewestError.value 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
  P haP v b hvb Z htarget hstop F hF hFm

open HistoryProductMeasure OrderedHeatForests
open ActualMeanKernel
local notation "Active"=>MixedPastNewestFields.active 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
  P haP v b hvb Z htarget hstop F hF hFm

def output (k:ℕ)(θ:ℝ)(q:ℝ≥0)(e:Ω×HeatCircle→ℝ)(z:X×Ω):ℝ:=
  ∫t:Fin k→ℝ,MixedPastNewestAverage.spatial 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
    P haP v b hvb Z htarget hstop F hF hFm k θ q e z.1 (t,z.2)
      ∂Measure.pi (fun _=>volume.restrict (Ioc (v:ℝ) (b:ℝ)))

theorem output_measurable (k:ℕ)(θ:ℝ)(q:ℝ≥0)(e:Ω×HeatCircle→ℝ)(he:Measurable e):
    Measurable (output 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
      P haP v b hvb Z htarget hstop F hF hFm k θ q e):=by
  have hm:=MixedPastNewestFields.active_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
    P haP v b hvb Z htarget hstop F hF hFm k θ q e he
  let W:=(X×Ω)×(Fin k→ℝ)
  have hmap:Measurable (fun z:W×(Fin k→HeatCircle)=>
      (z.1.1.2,separated k (z.1.1.1,z.1.2,z.2))):=measurable_fst.fst.snd.prodMk
    ((separated_measurable k).comp
      (measurable_fst.fst.fst.prodMk (measurable_fst.snd.prodMk measurable_snd)))
  have hsp:=((hm.comp hmap).stronglyMeasurable.integral_prod_right'
    (ν:=Measure.pi (fun _:Fin k=>haarAddCircle))).measurable
  have hh:=(hsp.stronglyMeasurable.integral_prod_right'
    (ν:=Measure.pi (fun _:Fin k=>volume.restrict (Ioc (v:ℝ) (b:ℝ))))).measurable
  exact hh

def constant (B Hr:ℝ)(k:ℕ)(B0:ℝ≥0)(A0 ν:ℝ):ℝ:=
  MixedPastNewestCollision.constant κ (M:=M) P B Hr k B0*(Fintype.card (Choices 1 k):ℝ)^2*
    (PastNewestTimeIntegral.currentConstant P (fraction P*P.lower) (uniformConstant 1) 1 k
      ((b:ℝ)-(v:ℝ)) (P.exponent/8) A0 ν)^2

include hIJ₀ hIJ₁ in
/-- Actual retained-root/sample energy after old-space and old-time
averaging, with the common current-q RMS envelope and no time cutoff. -/
theorem energy {B Hr:ℝ}(hB:0≤B)(hHr:0≤Hr)
    (hroot:∀x z,|F x z|≤B)
    (hrootmod:∀x z w,|F x z-F x w|≤Hr*|z 0-w 0|^P.exponent)
    (hlocal:StandardTerminalPastLocality J)(hΛ:0≤Λ)
    (hages:∀x i,(Z.observations x i).stop≤(Z.observations x i).target)
    (hrootStop:∀x i,(Z.observations x i).stop≤(b:ℝ))
    (hrootTarget:∀x i,(Z.observations x i).target=(b:ℝ))
    (hspan:(b:ℝ)-(v:ℝ)≤P.horizon)(ρ:Measure X)[IsProbabilityMeasure ρ](k:ℕ)
    (hold:∀j,j<k→(b:ℝ)-(v:ℝ)≤uniformHorizon 1 j)
    (x0:X)(q:ℝ≥0)(hvq:v≤q)(hqH:q≤H)(hqb:q<b)
    (A0 ν:ℝ)(hA:0≤A0)(hν:0≤ν)
    (hjet:∀x j,j≤k→∀z,‖iteratedFDeriv ℝ j (F x) z‖≤A0*ν^j)
    (B0:ℝ≥0)(hBDG:StandardTerminalBDGPower (k+2) J B0)
    (ε:ℝ)(hε:0≤ε)(e:Ω×HeatCircle→ℝ)(he:Measurable e)(hecap:∀p,|e p|≤ε)(θ:ℝ)(hθ:|θ|≤1):
    Integrable (fun z:X×Ω=>|output 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
      P haP v b hvb Z htarget hstop F hF hFm k θ q e z|^2) (ρ.prod μ) ∧
    (∫z:X×Ω,|output 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
      P haP v b hvb Z htarget hstop F hF hFm k θ q e z|^2 ∂ρ.prod μ)≤
        ε^2*constant κ (M:=M) P v b B Hr k B0 A0 ν*((b:ℝ)-q)^(P.exponent/4-2):=by
  obtain ⟨K,hK,hKmass,havg⟩:=MixedPastNewestAverage.energy_ae
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S J hIJ₀ hIJ₁ P haP v b hvb Z htarget hstop F hF hFm
    hB hHr hroot hrootmod hlocal hΛ hages hrootStop hrootTarget hspan ρ k hold x0 q hvq hqH hqb A0 ν hA hν hjet B0 hBDG
  let C0:=MixedPastNewestCollision.constant κ (M:=M) P B Hr k B0*(Fintype.card (Choices 1 k):ℝ)^2
  let C1:=PastNewestTimeIntegral.currentConstant P (fraction P*P.lower) (uniformConstant 1) 1 k
    ((b:ℝ)-(v:ℝ)) (P.exponent/8) A0 ν
  have hC0:0≤C0:=mul_nonneg (MixedPastNewestCollision.constant_nonneg κ (M:=M) P hB hHr k B0) (sq_nonneg _)
  have hf:0<P.exponent/8:=div_pos P.exponent_pos (by norm_num)
  have hf1:P.exponent/8≤1:=by linarith [P.exponent_le_one]
  have hcurr:=PastNewestTimeIntegral.current_bound Zero P (b:ℝ) (fun _=>rfl)
    (mul_pos (fraction_pos P) P.lower_pos) (uniformConstant 1) (fun j=>(uniformConstant_pos 1 j).le)
    k x0 (fun _=>0) (by exact_mod_cast hvq.trans_lt hqb) le_rfl hf hf1 hA hν
  have hKcap:K≤C1*((b:ℝ)-q)^(P.exponent/8-1):=by
    rw [hKmass]
    exact hcurr.2 q (by exact_mod_cast hvq) (by exact_mod_cast hqb)
  have hpow:(((b:ℝ)-q)^(P.exponent/8-1))^2=((b:ℝ)-q)^(P.exponent/4-2):=by
    rw [←Real.rpow_mul_natCast (sub_nonneg.mpr (show (q:ℝ)≤b by exact_mod_cast hqb.le))]
    congr 1
    ring
  let raw:X×Ω→ℝ:=output 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
    P haP v b hvb Z htarget hstop F hF hFm k θ q e
  have hm:Measurable raw:=output_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
    P haP v b hvb Z htarget hstop F hF hFm k θ q e he
  have hsec:∀ᵐx∂ρ,Integrable (fun ω=>‖raw (x,ω)‖^2) μ ∧
      (∫ω,‖raw (x,ω)‖^2 ∂μ)≤ε^2*C0*C1^2*((b:ℝ)-q)^(P.exponent/4-2):=by
    filter_upwards [havg ε hε e he hecap θ hθ] with x hx
    refine ⟨by simpa only [raw,output,Real.norm_eq_abs] using hx.2.1,?_⟩
    have hb:(∫ω,‖raw (x,ω)‖^2 ∂μ)≤ε^2*C0*K^2:=by
      convert! hx.2.2 using 1 <;> dsimp only [C0] <;> (try simp only [raw,output,Real.norm_eq_abs]) <;> ring
    have hh:=(hb.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hK hKcap 2)
      (mul_nonneg (sq_nonneg ε) hC0)))
    convert! hh using 1 <;> simp only [raw,output,Real.norm_eq_abs,mul_pow,hpow] <;> dsimp only [C0] <;> ring
  have hh:=SectionEnergy.product_energy μ ρ raw hm
    (fun _=>ε^2*C0*C1^2*((b:ℝ)-q)^(P.exponent/4-2)) (integrable_const _)
    (hsec.mono (fun _ h=>h.1)) (hsec.mono (fun _ h=>h.2))
  refine ⟨by simpa only [raw,Real.norm_eq_abs] using hh.1,?_⟩
  have hb:=hh.2
  simp only [integral_const,probReal_univ,one_smul,Real.norm_eq_abs] at hb
  convert! hb using 1 <;> dsimp only [constant,C0,C1] <;> ring

end SHE.MixedPastNewestCurrentEnergy
