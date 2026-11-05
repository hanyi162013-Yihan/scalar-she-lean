module

public import SHE.MovingComparisonHilbertSums
public import SHE.MovingComparisonSummability
public import SHE.RootSmoothSums
public import SHE.MovingComparisonFrequency
public import SHE.MovingComparisonGlobal
public import SHE.MovingComparisonField
public import SHE.ThreeLegEnergyIntegration
public import SHE.MovingComparisonSection
public import SHE.MovingMarkRootGlobalEnergy
public import SHE.MovingMeanGlobalL2
public import SHE.NegativeThreeLeg
public import SHE.MixedPastMeanRootL1
public import SHE.MovingRootThreeLeg
public import SHE.MovingMeanRootRealization
public import SHE.MovingCovarianceRootSections
public import SHE.MovingBaselineRootSections
public import SHE.MixedPastMeanThetaFourier
public import SHE.MovingMeanThetaEnergy
public import SHE.MovingMeanSectionEnergy
public import SHE.MeanThetaAverage
public import SHE.MovingMeanCost

@[expose] public section
noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
set_option quotPrecheck false

namespace SHE.MovingComparisonCutoffIdentity
open RootSmoothSums
open AddCircle
open MeasureTheory PredictableL2 NativeHeatObservation NativeObservationNaturality
open FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation StoppedItoInputs
open scoped NNReal ENNReal
local instance movingComparisonCutoffIdentity_realSigma : MeasurableSpace RealL2 := borel _
local instance movingComparisonCutoffIdentity_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance movingComparisonCutoffIdentity_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance movingComparisonCutoffIdentity_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance movingComparisonCutoffIdentity_blockSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance movingComparisonCutoffIdentity_blockBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
variable {Ω : Type} [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
variable (Λ κ : ℝ) (hκ : 0<κ) {aU aV : ℝ→ℝ} (haU : Measurable aU) (haV : Measurable aV) {ell M : ℝ}
variable (hell : 0<ell) (hbU : ∀ z,ell≤aU z ∧ aU z≤M) (hbV : ∀ z,ell≤aV z ∧ aV z≤M)
variable (I₀ I₁ : StandardTerminalIto (C := RealHaarIntegrand.Columns) (E := RealL2) 𝓕 μ H)
variable (u₀ : RealL2)
variable (S : MixedNativeAdditiveResidualPair.Solution 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀)

local instance movingComparisonCutoffIdentity_circleSigma : MeasurableSpace CircleL2 := borel _
local instance movingComparisonCutoffIdentity_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩
local instance movingComparisonCutoffIdentity_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
local instance movingComparisonCutoffIdentity_twoFinite : Fact ((2:ℝ≥0∞)≠∞) := ⟨by simp⟩
variable {W : Type} [MeasurableSpace W]



open Set CutoffWordLevel CutoffWordHistories ControlledProfile SmoothCylinders UniformSmooth
  PhysicalScoreChain ControlledOldIntervals
variable (P : CanonicalCovariance.ProfileParameters) (haP : BoundedSmooth P.coefficient)
variable (h : ℝ≥0) (Z : VariableObservations.Family HeatCircle 1)
variable (htarget : ∀ x i,(h:ℝ)≤(Z.observations x i).target)
variable (hstop : ∀ x i,(h:ℝ)≤(Z.observations x i).stop)
variable (F : ℕ→HeatCircle→WordRecursion.State 1→ℝ) (hF : ∀ j,UniformBoundedSmooth (F j))
variable (hFm : ∀ j,Measurable (fun z : HeatCircle×WordRecursion.State 1=>F j z.1 z.2))




variable (J : StandardTerminalIto (C:=Both RealHaarInput) (E:=ℝ) 𝓕 μ H)
variable (hIJ₀ : StandardScalarNaturality I₀ (leftIntegral 𝓕 μ H J))
variable (hIJ₁ : StandardScalarNaturality I₁ (rightIntegral 𝓕 μ H J))

local notation "Out"=>MovingComparisonHilbert.field 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h Z htarget hstop
local notation "Raw"=>MovingComparisonHilbert.scalarField 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h Z htarget hstop

include hIJ₀ hIJ₁ in
theorem actual_cutoff_identity (hlocal : StandardTerminalPastLocality J) (hΛ : 0<Λ)
    (hH : (H:ℝ)≤1)
    (hsmallPoint : ProfileStability.memoryConstant P.lower P.holder P.exponent*
      ProfileVolterra.powerConstant ((P.exponent-2)/4)*P.horizon^(P.exponent/4)≤1/2)
    (hsmallL2 : ProfileStability.memoryConstant P.lower P.holder P.exponent*
      ProfileVolterra.powerConstant ((P.exponent-1)/4)*P.horizon^(P.exponent/4)≤1/2)
    (hages : ∀ x i,(Z.observations x i).stop≤(Z.observations x i).target)
    (hrootStop : ∀ x i,(Z.observations x i).stop≤(h:ℝ))
    (hrootTarget : ∀ x i,(Z.observations x i).target=(h:ℝ))
    (hcenter : ∀ x,(Z.observations x 0).center=x)
    (hspan : (h:ℝ)≤P.horizon) (k : ℕ)
    (hfresh : (h:ℝ)≤UniformFutureProfileScores.horizon (1+k))
    (hold : ∀ j,j<k→(h:ℝ)≤uniformHorizon 1 j)
    (Bpast Babs : ℝ≥0) (hBDGpast : StandardTerminalBDGPower 1 J Bpast)
    (hBDGabs : StandardTerminalBDGPower (k+2) J Babs)
    (χ : ℝ) (hχ0 : 0≤χ) (hχ1 : χ<1) (p : ℕ) (hp : 0<p) (horder : 1≤(p:ℝ)*(1-χ))
    (B0 : ℝ≥0) (hBDG : StandardTerminalBDGPower ((2*p)*(k+2)) J B0)
    (mass ρ : ℝ) (hmass : 1≤mass) (hρ : 0<ρ) (hρhalf : ρ<1/2) (a : Finset ℕ) :
    Out (rootSum F a) (rootSum_uniform F hF a) (rootSum_measurable F hFm a) k mass ρ=ᵐ[
      (volume.restrict (Ioc (0:ℝ) (H:ℝ))).prod ((volume.restrict (Ioc (0:ℝ) (h:ℝ))).prod μ)]
      fun z=>∑ j∈a,Out (F j) (hF j) (hFm j) k mass ρ z := by
  have hm (G : HeatCircle→WordRecursion.State 1→ℝ) (hg : UniformBoundedSmooth G)
      (hgm : Measurable (fun z : HeatCircle×WordRecursion.State 1=>G z.1 z.2)) :
      Measurable (Out G hg hgm k mass ρ):=
    MovingComparisonHilbert.field_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
      P haP h Z htarget hstop G hg hgm hΛ.le hsmallPoint k mass ρ
  have hzero (G : HeatCircle→WordRecursion.State 1→ℝ) (hg : UniformBoundedSmooth G)
      (hgm : Measurable (fun z : HeatCircle×WordRecursion.State 1=>G z.1 z.2))
      (v s : ℝ) (ω : Ω) (hv : ¬MovingMeanPhysicalField.valid H h v s) :
      Out G hg hgm k mass ρ (v,(s,ω))=0 := by
    have hz (x : HeatCircle) : MovingComparisonField.field 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
        P haP h Z htarget hstop G hg hgm k (v,(s,(ω,x)))=0:=
      MovingComparisonField.field_zero_of_not_valid 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
        P haP h Z htarget hstop G hg hgm k _ hv
    have he : ‖Out G hg hgm k mass ρ (v,(s,ω))‖^2=0 := by
      rw [MovingComparisonHilbert.field_norm_sq 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
        P haP h Z htarget hstop G hg hgm k mass ρ hmass]
      simp only [MovingComparisonField.energy,NativeFourierAverage.scalarEnergy,hz,
        Complex.ofReal_zero,fourierCoeff,smul_zero,integral_zero,norm_zero,
        zero_pow (by decide : (2:ℕ)≠0),mul_zero,tsum_zero]
    exact norm_eq_zero.mp (sq_eq_zero_iff.mp he)
  have hevent : MeasurableSet {z : ℝ×(ℝ×Ω)|
      Out (rootSum F a) (rootSum_uniform F hF a) (rootSum_measurable F hFm a) k mass ρ z=
        ∑ j∈a,Out (F j) (hF j) (hFm j) k mass ρ z}:=
    measurableSet_eq_fun (hm _ (rootSum_uniform F hF a) (rootSum_measurable F hFm a))
      (Finset.measurable_sum a (fun j _=>hm (F j) (hF j) (hFm j)))
  have hsection (v s : ℝ) : ∀ᵐ ω ∂μ,
      Out (rootSum F a) (rootSum_uniform F hF a) (rootSum_measurable F hFm a) k mass ρ (v,(s,ω))=
        ∑ j∈a,Out (F j) (hF j) (hFm j) k mass ρ (v,(s,ω)) := by
    by_cases hv : MovingMeanPhysicalField.valid H h v s
    · have hh:=MovingComparisonHilbertSums.section_sum_ae 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
        P haP h Z htarget hstop F hF hFm J hIJ₀ hIJ₁ hlocal hΛ hH hsmallPoint hsmallL2
        hages hrootStop hrootTarget hcenter hspan k hfresh hold Bpast Babs hBDGpast hBDGabs
        χ hχ0 hχ1 p hp horder B0 hBDG mass ρ hmass hρ hρhalf (Real.toNNReal v) (Real.toNNReal s)
        (by change ((Real.toNNReal v:ℝ≥0):ℝ)+(h:ℝ)≤(H:ℝ)
            simpa only [Real.toNNReal_of_nonneg hv.1,NNReal.coe_mk] using hv.2.2.2)
        (by change (0:ℝ)<((Real.toNNReal s:ℝ≥0):ℝ)
            simpa only [Real.toNNReal_of_nonneg hv.2.1.le,NNReal.coe_mk] using hv.2.1)
        (by change ((Real.toNNReal s:ℝ≥0):ℝ)<(h:ℝ)
            simpa only [Real.toNNReal_of_nonneg hv.2.1.le,NNReal.coe_mk] using hv.2.2.1) a
      simpa only [Filter.EventuallyEq,Real.toNNReal_of_nonneg hv.1,
        Real.toNNReal_of_nonneg hv.2.1.le,NNReal.coe_mk] using hh
    · exact ae_of_all _ (fun ω=>by
        rw [hzero _ (rootSum_uniform F hF a) (rootSum_measurable F hFm a) v s ω hv]
        simp_rw [hzero (F _) (hF _) (hFm _) v s ω hv]
        exact Finset.sum_const_zero.symm)
  apply (Measure.ae_prod_iff_ae_ae hevent).mpr
  exact ae_of_all _ (fun v=>
    (Measure.ae_prod_iff_ae_ae (hevent.preimage (measurable_const.prodMk measurable_id))).mpr
      (ae_of_all _ (fun s=>hsection v s)))

end SHE.MovingComparisonCutoffIdentity
