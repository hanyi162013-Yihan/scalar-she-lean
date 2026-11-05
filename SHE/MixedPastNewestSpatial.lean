module
public import SHE.MixedPastNewestCollision
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
namespace SHE.MixedPastNewestSpatial
open Set MeasureTheory ProbabilityTheory Real AddCircle PredictableL2 NativeHeatObservation NativeObservationNaturality
  FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation StoppedItoInputs
  GaussianIncrement ControlledOldIntervals MeasurableGaussianScores PhysicalProfile
  WordRecursion CutoffWordLevel CutoffWordHistories CutoffCarriers PhysicalScoreChain PhysicalChainArrays
  PhysicalParentGeometry ControlledProfile ControlledReferenceLevel ControlledReferenceWindows
  ControlledFamilyProfileForest CoveredHistoryGeometry CoveredControlledLaw SmoothCylinders UniformSmooth GaussianConvolution
open scoped NNReal ENNReal BigOperators
local instance mixedPastNewestSpatial_realSigma : MeasurableSpace RealL2:=borel _
local instance mixedPastNewestSpatial_realBorel : BorelSpace RealL2:=⟨rfl⟩
local instance mixedPastNewestSpatial_rowSigma : MeasurableSpace RealHaarInput:=borel _
local instance mixedPastNewestSpatial_rowBorel : BorelSpace RealHaarInput:=⟨rfl⟩
local instance mixedPastNewestSpatial_bothSigma : MeasurableSpace (Both RealHaarInput):=borel _
local instance mixedPastNewestSpatial_bothBorel : BorelSpace (Both RealHaarInput):=⟨rfl⟩
local instance mixedPastNewestSpatial_circleSigma : MeasurableSpace CircleL2:=borel _
local instance mixedPastNewestSpatial_circleBorel : BorelSpace CircleL2:=⟨rfl⟩
local instance mixedPastNewestSpatial_period : Fact (0<2*π):=⟨by positivity⟩
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
local notation "Active"=>MixedPastNewestFields.active 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
  P haP v b hvb Z htarget hstop F hF hFm

include hIJ₀ hIJ₁ in
/-- Actual old-space Minkowski for the current-dependent newest error.
Only one parent-forest mass is paid, before the sample square. -/
theorem energy_ae {B Hr:ℝ}(hB:0≤B)(hHr:0≤Hr)
    (hroot:∀x z,|F x z|≤B)
    (hrootmod:∀x z w,|F x z-F x w|≤Hr*|z 0-w 0|^P.exponent)
    (hlocal:StandardTerminalPastLocality J)(hΛ:0≤Λ)
    (hages:∀x i,(Z.observations x i).stop≤(Z.observations x i).target)
    (hrootStop:∀x i,(Z.observations x i).stop≤(b:ℝ))
    (hspan:(b:ℝ)-(v:ℝ)≤P.horizon)(ρ:Measure X)[IsFiniteMeasure ρ](k:ℕ):
    ∀ᵐx∂ρ,∀ᵐt:Fin k→ℝ∂Measure.pi (fun _=>volume.restrict (Ioc (v:ℝ) (b:ℝ))),
      let a:=separated k (x,t,fun _=>0)
      ∀q:ℝ≥0,v≤q→q≤H→(q:ℝ)<(carrier Zero k).terminal a→
      ∀hp:StrictHistory Zero k a,SmallHistory Zero (uniformHorizon 1) k a→
      ∀θ:ℝ,|θ|≤1→∀A0 ν:ℝ,0≤A0→0≤ν→
      (∀j,j≤k→∀z,‖iteratedFDeriv ℝ j (F x) z‖≤A0*ν^j)→
      ∀B0:ℝ≥0,StandardTerminalBDGPower (k+2) J B0→
      ∀ε:ℝ,0≤ε→∀e:Ω×HeatCircle→ℝ,Measurable e→(∀p,|e p|≤ε)→
      let G:=fun ω=>∫w:Fin k→HeatCircle,Active k θ q e (ω,replaceSpace k a w)
        ∂Measure.pi (fun _=>haarAddCircle)
      Integrable (fun ω=>|G ω|^2) μ ∧
      (∫ω,|G ω|^2 ∂μ)≤ε^2*MixedPastNewestCollision.constant κ (M:=M) P B Hr k B0*
        (Fintype.card (Choices 1 k):ℝ)^2*timeWeight Zero (fraction P*P.lower) (uniformConstant 1) k a^2*
          PastWordTimeFields.total Zero P k a A0 ν*((carrier Zero k).terminal a-q)^(P.exponent/4-2):=by
  have hmodel:=MixedPastNewestCollision.energy_ae
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S J hIJ₀ hIJ₁
      P haP v b hvb Z htarget hstop F hF hFm hB hHr hroot hrootmod hlocal hΛ hages hrootStop hspan ρ k
  have hsections:=ae_replaceSpace_sections _ ρ k hmodel
  filter_upwards [hsections] with x hx
  filter_upwards [hx] with t ht
  intro a q hvq hqH hqt hp hsmall θ hθ A0 ν hA0 hν hjet B0 hBDG ε hε e he hecap G
  let η:Measure (Fin k→HeatCircle):=Measure.pi (fun _:Fin k=>haarAddCircle)
  let K:=parentEnvelope Zero hages k a hp
  have hKm:Measurable K:=(parentEnvelope_continuous Zero hages k a hp).measurable
  have hKi:Integrable K η:=(parentEnvelope_continuous Zero hages k a hp).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)
  have hKn(w:Fin k→HeatCircle):0≤K w:=parentDensity_nonneg 2 (by norm_num) k _ _ _
  have hmass:(∫w,K w ∂η)=(Fintype.card (Choices 1 k):ℝ):=parentEnvelope_mass Zero hages k a hp
  let C0:=ε^2*MixedPastNewestCollision.constant κ (M:=M) P B Hr k B0*
    timeWeight Zero (fraction P*P.lower) (uniformConstant 1) k a^2*
      PastWordTimeFields.total Zero P k a A0 ν*((carrier Zero k).terminal a-q)^(P.exponent/4-2)
  have hC0:0≤C0:=mul_nonneg (mul_nonneg (mul_nonneg
    (mul_nonneg (sq_nonneg _) (MixedPastNewestCollision.constant_nonneg κ (M:=M) P hB hHr k B0))
      (sq_nonneg _)) (PastWordTimeFields.total_nonneg _ _ _ _ _ _)) (rpow_nonneg (sub_pos.mpr hqt).le _)
  let Fw:Ω×(Fin k→HeatCircle)→ℝ:=fun z=>Active k θ q e (z.1,replaceSpace k a z.2)
  have hFw:Measurable Fw:=(MixedPastNewestFields.active_measurable
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S P haP v b hvb Z htarget hstop F hF hFm
      k θ q e he).comp (measurable_fst.prodMk ((replaceSpace_measurable k a).comp measurable_snd))
  have hpoint:∀ᵐw∂η,Integrable (fun ω=>|Fw (ω,w)|^2) μ ∧
      (∫ω,|Fw (ω,w)|^2 ∂μ)≤C0*(K w)^2:=by
    filter_upwards [ht] with w hw
    have hpw:StrictHistory Zero k (replaceSpace k a w):=(replaceSpace_strict_iff Zero k a w).mpr hp
    have hsw:SmallHistory Zero (uniformHorizon 1) k (replaceSpace k a w):=
      (smallHistory_replaceSpace_iff Zero (uniformHorizon 1) k a w).mpr hsmall
    have hqw:(q:ℝ)<(carrier Zero k).terminal (replaceSpace k a w):=by simpa only [replaceSpace_terminal] using hqt
    have hh:=hw q hvq hqH hqw hpw hsw θ hθ A0 ν hA0 hν
      (by simpa only [replaceSpace_root,root_separated] using hjet) B0 hBDG ε hε e he hecap
    have hE:timeWeight Zero (fraction P*P.lower) (uniformConstant 1) k (replaceSpace k a w)*
        parentDensity 2 (by norm_num) k (targets Zero k (replaceSpace k a w))
          (carrier_orderedTimes Zero hages k (replaceSpace k a w) hpw) (centers Zero k (replaceSpace k a w))=
      timeWeight Zero (fraction P*P.lower) (uniformConstant 1) k a*K w:=by
      rw [timeWeight_replaceSpace]
      apply congrArg (fun r:ℝ=>timeWeight Zero (fraction P*P.lower) (uniformConstant 1) k a*r)
      exact (ParentMeanDensity.parentProduct_eq_parentDensity Zero hages k (replaceSpace k a w) hpw).symm.trans
        (ParentMeanDensity.parentProduct_replaceSpace_eq Zero hages k a hp w)
    dsimp only at hh
    change Integrable (fun ω=>|Value k θ q (replaceSpace k a w) e ω|^2) μ ∧ _ at hh
    refine ⟨?_,?_⟩
    · simpa only [Fw,MixedPastNewestFields.active,if_pos hqw] using hh.1
    · have hb:=hh.2
      rw [hE] at hb
      change _≤ε^2*MixedPastNewestCollision.constant κ (M:=M) P B Hr k B0*
        (timeWeight Zero (fraction P*P.lower) (uniformConstant 1) k a*K w)^2*
          PastWordTimeFields.total Zero P k (replaceSpace k a w) A0 ν*
            ((carrier Zero k).terminal (replaceSpace k a w)-q)^(P.exponent/4-2) at hb
      rw [PastWordTimeFields.total_replaceSpace,replaceSpace_terminal] at hb
      convert! hb using 1 <;> simp only [Fw,MixedPastNewestFields.active,if_pos hqw] <;>
        dsimp only [C0] <;> ring
  have hh:=WeightedSFiniteMoments.nonnegative_envelope μ η Fw hFw K hKm hKi hKn 1 (by norm_num) C0 hC0
    (by simpa only [show 2*1=2 by rfl] using hpoint.mono (fun _ h=>h.1))
    (by simpa only [show 2*1=2 by rfl] using hpoint.mono (fun _ h=>h.2))
  refine ⟨by simpa only [show 2*1=2 by rfl,G,Fw,η] using hh.1,?_⟩
  have hb:=hh.2
  rw [hmass] at hb
  convert! hb using 1 <;> simp only [show 2*1=2 by rfl,G,Fw,η] <;> dsimp only [C0] <;> ring

end SHE.MixedPastNewestSpatial
