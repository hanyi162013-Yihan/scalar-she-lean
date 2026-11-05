module
public import SHE.MixedPastNewestInterpolation

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 2600000
namespace SHE.MixedPastNewestCollision
open Set MeasureTheory ProbabilityTheory Real AddCircle PredictableL2 NativeHeatObservation NativeObservationNaturality
  FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation StoppedItoInputs
  GaussianIncrement ControlledOldIntervals MeasurableGaussianScores PhysicalProfile
  WordRecursion CutoffWordLevel CutoffWordHistories CutoffCarriers PhysicalScoreChain PhysicalChainArrays
  PhysicalParentGeometry ControlledProfile ControlledReferenceLevel ControlledReferenceWindows
  ControlledFamilyProfileForest CoveredHistoryGeometry CoveredControlledLaw SmoothCylinders UniformSmooth GaussianConvolution
open scoped NNReal ENNReal BigOperators
local instance mixedPastNewestCollision_realSigma : MeasurableSpace RealL2:=borel _
local instance mixedPastNewestCollision_realBorel : BorelSpace RealL2:=⟨rfl⟩
local instance mixedPastNewestCollision_rowSigma : MeasurableSpace RealHaarInput:=borel _
local instance mixedPastNewestCollision_rowBorel : BorelSpace RealHaarInput:=⟨rfl⟩
local instance mixedPastNewestCollision_bothSigma : MeasurableSpace (Both RealHaarInput):=borel _
local instance mixedPastNewestCollision_bothBorel : BorelSpace (Both RealHaarInput):=⟨rfl⟩
local instance mixedPastNewestCollision_circleSigma : MeasurableSpace CircleL2:=borel _
local instance mixedPastNewestCollision_circleBorel : BorelSpace CircleL2:=⟨rfl⟩
local instance mixedPastNewestCollision_period : Fact (0<2*π):=⟨by positivity⟩
attribute [local irreducible] MixedPastNewestError.value WordRecursion.directionalSecond
  GaussianConvolution.gaussianAverage UncutSmoothWords.test MeasurableGaussianScores.scoreVariance
  MeasurableGaussianScores.coefficient MeasurableGeneralizedInverse.generalizedInverse
variable {Ω:Type*}[MeasurableSpace Ω]{X:Type}[MeasurableSpace X]
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

def constant (B Hr:ℝ)(k:ℕ)(B0:ℝ≥0):ℝ:=
  sqrt (MixedPastWordMoments.momentConstant P k k 1
    ((k:ℝ)*(NativeHybridMoments.momentConstant (k+2) B0 κ M)^P.exponent))*
      (2:ℝ)^k*((1+k:ℕ):ℝ)/(2*P.lower)*MixedPastNewestInterpolation.holderCost P B Hr k

theorem constant_nonneg {B Hr:ℝ}(hB:0≤B)(hHr:0≤Hr)(k:ℕ)(B0:ℝ≥0):
    0≤constant κ (M:=M) P B Hr k B0:=by
  unfold constant
  exact mul_nonneg (div_nonneg (mul_nonneg (mul_nonneg (sqrt_nonneg _) (pow_nonneg (by norm_num) _))
    (Nat.cast_nonneg _)) (mul_nonneg (by norm_num) P.lower_pos.le))
      (MixedPastNewestInterpolation.holderCost_nonneg P hB hHr k)

include hIJ₀ hIJ₁ in
/-- The true current-dependent newest coefficient error has an integrable
fresh collision exponent. The old parent density occurs once after taking
the square root; every old rough block retains half its original minimum gain. -/
theorem energy_ae {B Hr:ℝ}(hB:0≤B)(hHr:0≤Hr)
    (hroot:∀x z,|F x z|≤B)
    (hrootmod:∀x z w,|F x z-F x w|≤Hr*|z 0-w 0|^P.exponent)
    (hlocal:StandardTerminalPastLocality J)(hΛ:0≤Λ)
    (hages:∀x i,(Z.observations x i).stop≤(Z.observations x i).target)
    (hrootStop:∀x i,(Z.observations x i).stop≤(b:ℝ))
    (hspan:(b:ℝ)-(v:ℝ)≤P.horizon)(ρ:Measure X)[IsFiniteMeasure ρ](k:ℕ):
    ∀ᵐh∂historyMeasure (referenceData P P.coefficient haP Λ 0 v b hvb (0,0)) ρ k,
      ∀q:ℝ≥0,v≤q→q≤H→(q:ℝ)<(carrier Zero k).terminal h→
      ∀hp:StrictHistory Zero k h,SmallHistory Zero (uniformHorizon 1) k h→
      ∀θ:ℝ,|θ|≤1→∀A0 ν:ℝ,0≤A0→0≤ν→
      (∀j,j≤k→∀z,‖iteratedFDeriv ℝ j (F (rootParameter k h)) z‖≤A0*ν^j)→
      ∀B0:ℝ≥0,StandardTerminalBDGPower (k+2) J B0→
      ∀ε:ℝ,0≤ε→∀e:Ω×HeatCircle→ℝ,Measurable e→(∀p,|e p|≤ε)→
      let oldEnvelope:=timeWeight Zero (fraction P*P.lower) (uniformConstant 1) k h*
        OrderedHeatForests.parentDensity 2 (by norm_num) k (targets Zero k h)
          (carrier_orderedTimes Zero hages k h hp) (centers Zero k h)
      let sharp:=MixedPastWordMoments.total (d:=1) P
        (fun j=>lower Zero k h j-(v:ℝ)) (fun j=>upper Zero k h j-(v:ℝ))
        (fun j=>targets Zero k h (leafIndex k (fun i=>i) j)-(v:ℝ)) A0 ν
      Integrable (fun ω=>|Value k θ q h e ω|^2) μ ∧
        (∫ω,|Value k θ q h e ω|^2 ∂μ)≤ε^2*constant κ (M:=M) P B Hr k B0*
          oldEnvelope^2*sharp*((carrier Zero k).terminal h-q)^(P.exponent/4-2) := by
  filter_upwards [MixedPastNewestError.good_energy_ae
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S J hIJ₀ hIJ₁
      P haP v b hvb Z htarget hstop F hF hFm hlocal hΛ hages hrootStop hspan ρ k,
    MixedPastNewestInterpolation.bad_bound_ae
      𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
      P haP v b hvb Z htarget hstop F hF hFm hB hHr hroot hrootmod hages hspan ρ k]
      with h hg hb
  intro q hvq hqH hqt hp hsmall θ hθ A0 ν hA0 hν hjet B0 hBDG ε hε e he hecap
  dsimp only
  let K:=timeWeight Zero (fraction P*P.lower) (uniformConstant 1) k h*
    OrderedHeatForests.parentDensity 2 (by norm_num) k (targets Zero k h)
      (carrier_orderedTimes Zero hages k h hp) (centers Zero k h)
  let T:=MixedPastWordMoments.total (d:=1) P
    (fun j=>lower Zero k h j-(v:ℝ)) (fun j=>upper Zero k h j-(v:ℝ))
    (fun j=>targets Zero k h (leafIndex k (fun i=>i) j)-(v:ℝ)) A0 ν
  let δ:ℝ:=(carrier Zero k).terminal h-q
  let C:=MixedPastWordMoments.momentConstant P k k 1
    ((k:ℝ)*(NativeHybridMoments.momentConstant (k+2) B0 κ M)^P.exponent)
  have hK:0≤K:=mul_nonneg
    (timeWeight_nonneg Zero (mul_pos (fraction_pos P) P.lower_pos) (uniformConstant 1)
      (fun j=>(uniformConstant_pos 1 j).le) k h hp)
    (OrderedHeatForests.parentDensity_nonneg 2 (by norm_num) k _ _ _)
  have hT:0≤T:=MixedPastWordMoments.total_nonneg _ _ _ _ _ _
  have hC:0≤C:=MixedPastWordMoments.momentConstant_nonneg _ _ _ _ _
  have hδ:0<δ:=sub_pos.mpr hqt
  have hg':=hg q hvq hqH hqt hp hsmall θ hθ A0 ν hA0 hν hjet B0 hBDG ε hε e he hecap
  change Integrable (fun ω=>|Value k θ q h e ω|^2) μ ∧
    (∫ω,|Value k θ q h e ω|^2 ∂μ)≤C*(K*T*(ε*((1+k:ℕ):ℝ)/((P.lower/2)*δ))/2)^2 at hg'
  let A:=sqrt C*(K*T*(ε*((1+k:ℕ):ℝ)/((P.lower/2)*δ))/2)
  let D:=(ε/2)*((2:ℝ)^k*K)*MixedPastNewestInterpolation.holderCost P B Hr k*δ^(P.exponent/4-1)
  have hA:0≤A:=mul_nonneg (sqrt_nonneg _) (div_nonneg (mul_nonneg (mul_nonneg hK hT)
    (div_nonneg (mul_nonneg hε (Nat.cast_nonneg _)) (mul_nonneg (div_nonneg P.lower_pos.le (by norm_num)) hδ.le)))
      (by norm_num))
  have hD:0≤D:=mul_nonneg (mul_nonneg (mul_nonneg (div_nonneg hε (by norm_num))
    (mul_nonneg (pow_nonneg (by norm_num) _) hK))
      (MixedPastNewestInterpolation.holderCost_nonneg P hB hHr k)) (rpow_nonneg hδ.le _)
  have hgood:(∫ω,|Value k θ q h e ω|^2 ∂μ)≤A^2:=by
    dsimp only [A]
    rw [mul_pow,Real.sq_sqrt hC]
    exact hg'.2
  have hbad:(∫ω,|Value k θ q h e ω|^2 ∂μ)≤D^2:=by
    have hh:=integral_mono_ae hg'.1 (integrable_const (D^2:ℝ))
      (ae_of_all μ (fun ω=>pow_le_pow_left₀ (abs_nonneg _) (hb q hvq hqt hp hsmall θ ε hε e he hecap ω) 2))
    simpa only [D,K,δ,integral_const,probReal_univ,one_smul] using hh
  have hfinal:=FreshMassInterpolation.two_caps hA hD hgood hbad
  have hrpow:δ^(P.exponent/4-1)=δ*δ^(P.exponent/4-2):=by
    calc
      _=δ^(1+(P.exponent/4-2)):=by congr 1 <;> ring
      _=δ^1*δ^(P.exponent/4-2):=Real.rpow_add hδ _ _
      _=_:=by rw [Real.rpow_one]
  refine ⟨hg'.1,hfinal.trans_eq ?_⟩
  dsimp only [A,D,C,constant,K,T,δ]
  change _=ε^2*(sqrt C*(2:ℝ)^k*((1+k:ℕ):ℝ)/(2*P.lower)*
    MixedPastNewestInterpolation.holderCost P B Hr k)*K^2*T*δ^(P.exponent/4-2)
  change (sqrt C*(K*T*(ε*((1+k:ℕ):ℝ)/((P.lower/2)*δ))/2))*
    ((ε/2)*((2:ℝ)^k*K)*MixedPastNewestInterpolation.holderCost P B Hr k*δ^(P.exponent/4-1))=_
  rw [hrpow]
  field_simp [P.lower_pos.ne',hδ.ne']
  <;> ring

end SHE.MixedPastNewestCollision
