module

public import SHE.MixedCanonicalGradientKernel
public import SHE.RecursiveHeatGradientContinuity
public import SHE.NativeRowTargetContinuity

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
set_option quotPrecheck false
namespace SHE.MixedCanonicalGradientHeat
open MeasureTheory Set PredictableL2 NativeHeatObservation NativeObservationNaturality
open FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation CutoffWordLevel
open GaussianTaylorAverage JointWordAnalytic GaussianItoTest ControlledProfile ControlledReferenceLevel
open scoped ENNReal NNReal
local instance mixedCanonicalGradientHeat_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
local instance mixedCanonicalGradientHeat_circleSigma : MeasurableSpace CircleL2 := borel _
local instance mixedCanonicalGradientHeat_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩
local instance mixedCanonicalGradientHeat_realSigma : MeasurableSpace RealL2 := borel _
local instance mixedCanonicalGradientHeat_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance mixedCanonicalGradientHeat_inputSigma : MeasurableSpace RealHaarInput := borel _
local instance mixedCanonicalGradientHeat_inputBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance mixedCanonicalGradientHeat_bothSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance mixedCanonicalGradientHeat_bothBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
variable {Ω : Type*} [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
variable (Λ κ : ℝ) (hκ : 0<κ) {aU aV : ℝ→ℝ} (haU : Measurable aU) (haV : Measurable aV) {ell M : ℝ}
variable (hell : 0<ell) (hbU : ∀ z,ell≤aU z ∧ aU z≤M) (hbV : ∀ z,ell≤aV z ∧ aV z≤M)
variable (I₀ I₁ : StandardTerminalIto (C := RealHaarIntegrand.Columns) (E := RealL2) 𝓕 μ H)
variable (u₀ v₀ : RealL2)
variable (S : MixedNativeAdditiveResidualPair.Solution 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀)

open ControlledProfile ControlledReferenceLevel
variable (P : CanonicalCovariance.ProfileParameters) (hAs : SmoothCylinders.BoundedSmooth (fun z => κ+aV z))
variable (θ : ℝ) (v b : ℝ≥0) (hvb : v≤b)
variable {n : ℕ} (Z : Fin n→WordRecursion.Observation)
variable (htarget : ∀ i,(b:ℝ)≤(Z i).target) (hstop : ∀ i,(b:ℝ)≤(Z i).stop)
variable (F : WordRecursion.State n→ℝ) (hF : SmoothCylinders.BoundedSmooth F)
variable (δ : ℝ) (hδ : 0<δ)
local notation "L" => ControlledReferenceRecursiveBounds.level P (fun z => κ+aV z) hAs Λ θ v b hvb Z htarget hstop F hF δ hδ

local notation "dU" => MixedNativeJointHistory.firstData 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
local notation "dV" => MixedNativeJointHistory.secondData 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
local notation "U" => (dU).physicalState
local notation "V" => (dV).physicalState
local notation "XU" => (dU).physicalField
local notation "XV" => (dV).physicalField

variable (hsmall : ProfileStability.memoryConstant P.lower P.holder P.exponent*
  ProfileVolterra.powerConstant ((P.exponent-2)/4)*P.horizon^(P.exponent/4)≤1/2)

local notation "pastParameter" => MixedNativeRandomReferenceStep.randomParameter 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S v
variable (J : StandardTerminalIto (C := Both RealHaarInput) (E := ℝ) 𝓕 μ H)
variable (hIJ₀ : StandardScalarNaturality I₀ (leftIntegral 𝓕 μ H J))
variable (hIJ₁ : StandardScalarNaturality I₁ (rightIntegral 𝓕 μ H J))

variable (hnull:NullCompleteFiltration.ContainsNullSets 𝓕 μ) (hΛ:0≤Λ) (hbH:b≤H)

variable (k:ℕ)
local notation "Obs" => (fun ε:ℝ≥0=>((L (0,0) ε k).observations.observations))
local notation "Terminal" => (fun ε:ℝ≥0=>((L (0,0) ε k).terminal))
local notation "Held"=>PredictablePastParameter.held v pastParameter (0,0)

local notation "Raw" => (fun ε:ℝ≥0=>MixedCanonicalGradientKernel.raw
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
  P hAs θ v b hvb Z htarget hstop F hF δ hδ ε k)
local notation "Mean" => (fun ε:ℝ≥0=>MixedCanonicalGradientKernel.mean
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
  P hAs θ v b hvb Z htarget hstop F hF δ hδ ε k)
local notation "Base" => ControlledReferenceLevel.level P (fun z=>κ+aV z) hAs Λ θ v b hvb
  Z htarget hstop F hF

include S in
private theorem target_continuous (h:CutoffWordHistories.History Unit k)(i:Fin (n+k)):
    Continuous (fun ε:ℝ≥0=>(Obs ε h i).target):=
  RecursiveHeatTargets.target_continuous (Base (0,0)) δ hδ k h i
include S in
private theorem center_eq (ε:ℝ≥0)(h:CutoffWordHistories.History Unit k)(i:Fin (n+k)):
    ((L (0,0) ε k).observations.observations h i).center=((L (0,0) 0 k).observations.observations h i).center:=
  RecursiveHeatTargets.center_eq (Base (0,0)) δ hδ ε 0 k h i
include S in
private theorem stop_eq (ε:ℝ≥0)(h:CutoffWordHistories.History Unit k)(i:Fin (n+k)):
    ((L (0,0) ε k).observations.observations h i).stop=((L (0,0) 0 k).observations.observations h i).stop:=
  RecursiveHeatTargets.stop_eq (Base (0,0)) δ hδ ε 0 k h i
include S in
private theorem terminal_eq (ε:ℝ≥0)(h:CutoffWordHistories.History Unit k):
    (L (0,0) ε k).terminal h=(L (0,0) 0 k).terminal h:=
  ControlledReferenceRecursiveBounds.terminal_eq P (fun z=>κ+aV z) hAs Λ θ v b hvb
    Z htarget hstop F hF δ hδ (0,0) (0,0) ε 0 k h

/-- The complete physical current vector converges with the moving
finite recursive history when the heat age vanishes. Every coordinate
has positive age strictly before its original terminal. -/
theorem mean_continuous (z:CutoffWordHistories.History Unit k×(ℝ≥0×Ω))
    (hz:(z.2.1:ℝ)<Terminal 0 z.1):
    Continuous (fun ε:ℝ≥0=>Mean ε z):=by
  apply (PiLp.continuous_toLp 2 (fun _:Fin (n+k)=>ℝ)).comp
  apply continuous_pi
  intro i
  have hg(ε:ℝ≥0):(z.2.1:ℝ)<(Obs ε z.1 i).target:=by
    have hh:=(L (0,0) ε k).targets_after z.1 i
    rw [terminal_eq 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
      P hAs θ v b hvb Z htarget hstop F hF δ hδ k ε z.1] at hh
    exact hz.trans_le hh
  have hu:Continuous (fun ε:ℝ≥0=>PhysicalProfile.physicalHeatMean
      (embed (S.first z.2.1 z.2.2)) ((Obs ε z.1 i).target-(z.2.1:ℝ),(Obs 0 z.1 i).center)):=by
    rw [continuous_iff_continuousAt]
    intro ε
    exact (ObservationTargetContinuity.continuousAt_heatMean_age (sub_pos.mpr (hg ε)) _ _).comp
      (f:=fun η:ℝ≥0=>(Obs η z.1 i).target-(z.2.1:ℝ)) (x:=ε)
      ((target_continuous 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
        P hAs θ v b hvb Z htarget hstop F hF δ hδ k z.1 i).sub continuous_const).continuousAt
  have hd:Continuous (fun ε:ℝ≥0=>PhysicalProfile.physicalHeatMean
      (embed (S.second z.2.1 z.2.2-S.first z.2.1 z.2.2))
        ((Obs ε z.1 i).target-(z.2.1:ℝ),(Obs 0 z.1 i).center)):=by
    rw [continuous_iff_continuousAt]
    intro ε
    exact (ObservationTargetContinuity.continuousAt_heatMean_age (sub_pos.mpr (hg ε)) _ _).comp
      (f:=fun η:ℝ≥0=>(Obs η z.1 i).target-(z.2.1:ℝ)) (x:=ε)
      ((target_continuous 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
        P hAs θ v b hvb Z htarget hstop F hF δ hδ k z.1 i).sub continuous_const).continuousAt
  convert hu.add (hd.const_mul (Real.exp (-Λ*((Obs 0 z.1 i).stop-(z.2.1:ℝ))))) using 1
  funext ε
  simp only [Function.comp_def,Pi.add_apply,Pi.mul_apply,Pi.sub_apply,Pi.smul_apply,MixedCanonicalGradientKernel.mean,WithLp.ofLp_toLp,
    center_eq 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S P hAs θ v b hvb Z htarget hstop F hF δ hδ k ε z.1 i,
    stop_eq 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S P hAs θ v b hvb Z htarget hstop F hF δ hδ k ε z.1 i]

private theorem row_continuous (z:CutoffWordHistories.History Unit k×(ℝ≥0×Ω))
    (hz:(z.2.1:ℝ)<Terminal 0 z.1)(i:Fin (n+k)):
    Continuous (fun ε:ℝ≥0=>MixedNativeJointPhysicalRows.physicalRow
      𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S (Obs ε z.1) z.2 i):=by
  have hg(ε:ℝ≥0):(z.2.1:ℝ)<(Obs ε z.1 i).target:=by
    have hh:=(L (0,0) ε k).targets_after z.1 i
    rw [terminal_eq 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
      P hAs θ v b hvb Z htarget hstop F hF δ hδ k ε z.1] at hh
    exact hz.trans_le hh
  have hr {l W:ℝ}(hl:0<l)(f:EllipticField l W):Continuous (fun ε:ℝ≥0=>
      NativeObservationCovariance.row hl f (Obs ε z.1 i).target (z.2.1:ℝ) (Obs 0 z.1 i).center):=by
    rw [continuous_iff_continuousAt]
    intro ε
    exact (NativeRowTargetContinuity.row_continuousAt_target hl f (hg ε) _).comp
      (f:=fun η:ℝ≥0=>(Obs η z.1 i).target) (x:=ε)
      (target_continuous 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
        P hAs θ v b hvb Z htarget hstop F hF δ hδ k z.1 i).continuousAt
  have h0:=hr hκ (AdditiveHaarForcing.constantField κ hκ)
  have hu:=hr hell (ContinuousHeatMild.coefficientFunction haU hell hbU S.first z.2)
  have hv:=hr hell (ContinuousHeatMild.coefficientFunction haV hell hbV S.second z.2)
  have hs:=WithLp.prod_continuous_toLp 2 RealHaarInput RealHaarInput |>.comp
    (h0.prodMk (hv.add ((hu.sub hv).const_smul (1-Real.exp (-Λ*((Obs 0 z.1 i).stop-(z.2.1:ℝ)))))))
  convert hs using 1
  funext ε
  simp only [Function.comp_def,Pi.add_apply,Pi.mul_apply,Pi.sub_apply,Pi.smul_apply,MixedNativeJointPhysicalRows.physicalRow,MixedNativeJointPhysicalRows.additiveRow,
    MixedNativeJointPhysicalRows.firstRow,MixedNativeJointPhysicalRows.secondRow,
    center_eq 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S P hAs θ v b hvb Z htarget hstop F hF δ hδ k ε z.1 i,
    stop_eq 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S P hAs θ v b hvb Z htarget hstop F hF δ hδ k ε z.1 i]

/-- Pointwise convergence of the literal predictable kth kernel, with
the whole recursive word, covariance and current varying with epsilon. -/
theorem raw_continuous (z:CutoffWordHistories.History Unit k×(ℝ≥0×Ω)):
    Continuous (fun ε:ℝ≥0=>Raw ε z):=by
  by_cases hvq:(v:ℝ)<(z.2.1:ℝ)
  · by_cases hq:(z.2.1:ℝ)<Terminal 0 z.1
    · have hMean:=mean_continuous 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
        P hAs θ v b hvb Z htarget hstop F hF δ hδ k z hq
      have hG:=RecursiveHeatGradientContinuity.continuous_gradient (Base (Held z.2)) δ hδ k z.1 (z.2.1:ℝ)
      have hh:=hG.comp (continuous_id.prodMk hMean)
      have hs:=continuous_finsetSum Finset.univ (fun i _=>
        (hh.clm_apply (continuous_const (y:=EuclideanSpace.basisFun (Fin (n+k)) ℝ i))).smul
          (row_continuous 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
            P hAs θ v b hvb Z htarget hstop F hF δ hδ k z hq i))
      convert hs using 1
      funext ε
      dsimp only
      rw [MixedCanonicalGradientKernel.raw,if_pos ⟨hvq,by
        rw [terminal_eq 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
          P hAs θ v b hvb Z htarget hstop F hF δ hδ k ε z.1];exact hq⟩]
      rfl
    · have he:(fun ε:ℝ≥0=>Raw ε z)=fun _=>0:=by
        funext ε
        dsimp only
        rw [MixedCanonicalGradientKernel.raw]
        apply if_neg
        rintro ⟨_,hh⟩
        rw [terminal_eq 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
          P hAs θ v b hvb Z htarget hstop F hF δ hδ k ε z.1] at hh
        exact hq hh
      rw [he];exact continuous_const
  · have he:(fun ε:ℝ≥0=>Raw ε z)=fun _=>0:=by
      funext ε
      dsimp only
      rw [MixedCanonicalGradientKernel.raw]
      exact if_neg (fun hh=>hvq hh.1)
    rw [he];exact continuous_const

end SHE.MixedCanonicalGradientHeat
