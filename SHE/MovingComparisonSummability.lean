module

public import SHE.MovingComparisonHilbert
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

namespace SHE.MovingComparisonSummability
open AddCircle
open MeasureTheory PredictableL2 NativeHeatObservation NativeObservationNaturality
open FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation StoppedItoInputs
open scoped NNReal ENNReal
local instance movingComparisonSummability_realSigma : MeasurableSpace RealL2 := borel _
local instance movingComparisonSummability_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance movingComparisonSummability_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance movingComparisonSummability_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance movingComparisonSummability_blockSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance movingComparisonSummability_blockBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
variable {Ω : Type} [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
variable (Λ κ : ℝ) (hκ : 0<κ) {aU aV : ℝ→ℝ} (haU : Measurable aU) (haV : Measurable aV) {ell M : ℝ}
variable (hell : 0<ell) (hbU : ∀ z,ell≤aU z ∧ aU z≤M) (hbV : ∀ z,ell≤aV z ∧ aV z≤M)
variable (I₀ I₁ : StandardTerminalIto (C := RealHaarIntegrand.Columns) (E := RealL2) 𝓕 μ H)
variable (u₀ : RealL2)
variable (S : MixedNativeAdditiveResidualPair.Solution 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀)

local instance movingComparisonSummability_circleSigma : MeasurableSpace CircleL2 := borel _
local instance movingComparisonSummability_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩
local instance movingComparisonSummability_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
local instance movingComparisonSummability_twoFinite : Fact ((2:ℝ≥0∞)≠∞) := ⟨by simp⟩
variable {W : Type} [MeasurableSpace W]



open Set CutoffWordLevel CutoffWordHistories ControlledProfile SmoothCylinders UniformSmooth
  PhysicalScoreChain ControlledOldIntervals
variable (P : CanonicalCovariance.ProfileParameters) (haP : BoundedSmooth P.coefficient)
variable (h : ℝ≥0) (Z : VariableObservations.Family HeatCircle 1)
variable (htarget : ∀ x i,(h:ℝ)≤(Z.observations x i).target)
variable (hstop : ∀ x i,(h:ℝ)≤(Z.observations x i).stop)
variable (F : HeatCircle→WordRecursion.State 1→ℝ) (hF : UniformBoundedSmooth F)
variable (hFm : Measurable (fun z : HeatCircle×WordRecursion.State 1=>F z.1 z.2))
local notation "AA"=>ControlledMeanOldAverageShift.absoluteAt P P.coefficient haP Λ h Z htarget hstop F hF hFm
local notation "ZT" v=>ObservationFamilyTimeShift.family (v:ℝ) Z
local notation "HT" v=>ControlledWordTimeShift.translatedTargets h Z htarget v
local notation "HS" v=>ControlledWordTimeShift.translatedStops h Z hstop v



local notation "Val"=>MovingMeanSectionEnergy.value 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
  P haP h Z htarget hstop F hF hFm

local notation "Avg"=>MovingMeanThetaEnergy.thetaValue 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
  P haP h Z htarget hstop F hF hFm
variable (J : StandardTerminalIto (C:=Both RealHaarInput) (E:=ℝ) 𝓕 μ H)
variable (hIJ₀ : StandardScalarNaturality I₀ (leftIntegral 𝓕 μ H J))
variable (hIJ₁ : StandardScalarNaturality I₁ (rightIntegral 𝓕 μ H J))

local notation "CT"=>MovingMarkRootTheta.covarianceTheta 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S
  P P.coefficient haP h Z htarget hstop F hF hFm
local notation "BT"=>MovingMarkRootTheta.baselineTheta 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S
  P P.coefficient haP h Z htarget hstop F hF hFm

local notation "End"=>MovingComparisonSection.endpointDifference 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
  P haP h Z htarget hstop F hF hFm
local notation "CF"=>MovingMarkRootTheta.covarianceField 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S
  P P.coefficient haP h Z htarget hstop F hF hFm
local notation "BF"=>MovingMarkRootTheta.baselineField 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S
  P P.coefficient haP h Z htarget hstop F hF hFm
local notation "MF"=>MovingMeanPhysicalField.field 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
  P haP h Z htarget hstop F hF hFm

local notation "Scalar"=>MovingComparisonHilbert.scalarField 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
  P haP h Z htarget hstop F hF hFm

include hIJ₀ hIJ₁ in
theorem section_summable (hlocal : StandardTerminalPastLocality J) (hΛ : 0<Λ)
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
    (A0 ν : ℝ) (hA0 : 0≤A0) (hν : 0≤ν)
    (hjet : ∀ x j,j≤k→∀ z,‖iteratedFDeriv ℝ j (F x) z‖≤A0*ν^j)
    (χ : ℝ) (hχ0 : 0≤χ) (hχ1 : χ<1) (p : ℕ) (hp : 0<p) (horder : 1≤(p:ℝ)*(1-χ))
    (Bpast Babs B0 : ℝ≥0) (hBDGpast : StandardTerminalBDGPower 1 J Bpast)
    (hBDGabs : StandardTerminalBDGPower (k+2) J Babs)
    (hBDG : StandardTerminalBDGPower ((2*p)*(k+2)) J B0)
    (mass ρ : ℝ) (hmass : 1≤mass) (hρ : 0<ρ) (hρhalf : ρ<1/2)
    (v s : ℝ≥0) (hvH : v+h≤H) (hs : 0<s) (hsh : s<h) :
    ∀ᵐ ω ∂μ,Summable (fun n : ℤ=>‖NativeNegativeRealization.coefficients mass ρ (Scalar k)
      ((v:ℝ),((s:ℝ),ω)) n‖^2) := by
  have hc:=MovingComparisonSection.actual_comparison 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
    P haP h Z htarget hstop F hF hFm J hIJ₀ hIJ₁ hlocal hΛ hH hsmallPoint hsmallL2
    hages hrootStop hrootTarget hcenter hspan k hfresh hold A0 ν hA0 hν hjet χ hχ0 hχ1 p hp horder
    Bpast Babs B0 hBDGpast hBDGabs hBDG mass ρ hmass hρ hρhalf v s hvH hs hsh
  have hf:=MovingComparisonField.field_eq_endpoint_ae 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
    P haP h Z htarget hstop F hF hFm J hIJ₀ hIJ₁ hlocal hΛ.le hH hsmallPoint hsmallL2
    hages hrootStop hrootTarget hcenter hspan k hfresh hold A0 ν hA0 hν hjet Bpast Babs hBDGpast hBDGabs
    v s hvH hs hsh
  filter_upwards [hc,Measure.ae_ae_of_ae_prod hf] with ω hω hωf
  apply hω.1.congr
  intro n
  rw [NativeNegativeRealization.coefficients_norm_sq mass ρ hmass]
  have he:=congrFun (fourierCoeff_congr_ae (hωf.mono (fun x hx=>congrArg Complex.ofReal hx))) n
  change (mass+(n:ℝ)^2)^(-ρ)*‖fourierCoeff (fun x=>Complex.ofReal (End k v s (ω,x))) n‖^2=_
  exact congrArg (fun c : ℂ=>(mass+(n:ℝ)^2)^(-ρ)*‖c‖^2) he.symm

include hIJ₀ hIJ₁ in
theorem product_summable (hlocal : StandardTerminalPastLocality J) (hΛ : 0<Λ)
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
    (A0 ν : ℝ) (hA0 : 0≤A0) (hν : 0≤ν)
    (hjet : ∀ x j,j≤k→∀ z,‖iteratedFDeriv ℝ j (F x) z‖≤A0*ν^j)
    (χ : ℝ) (hχ0 : 0≤χ) (hχ1 : χ<1) (p : ℕ) (hp : 0<p) (horder : 1≤(p:ℝ)*(1-χ))
    (Bpast Babs B0 : ℝ≥0) (hBDGpast : StandardTerminalBDGPower 1 J Bpast)
    (hBDGabs : StandardTerminalBDGPower (k+2) J Babs)
    (hBDG : StandardTerminalBDGPower ((2*p)*(k+2)) J B0)
    (mass ρ : ℝ) (hmass : 1≤mass) (hρ : 0<ρ) (hρhalf : ρ<1/2) :
    ∀ᵐ z ∂(volume.restrict (Ioc (0:ℝ) (H:ℝ))).prod ((volume.restrict (Ioc (0:ℝ) (h:ℝ))).prod μ),
      Summable (fun n : ℤ=>‖NativeNegativeRealization.coefficients mass ρ (Scalar k) z n‖^2) := by
  let C:=NativeNegativeRealization.coefficients mass ρ (Scalar k)
  have hm : ∀ n,Measurable (fun z=>C z n):=fun n=>measurable_const.mul
    (NativeFourierAverage.scalar_coefficient_measurable _
      (MovingComparisonHilbert.scalarField_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
        P haP h Z htarget hstop F hF hFm hΛ.le hsmallPoint k) n)
  have hevent : MeasurableSet {z : ℝ×(ℝ×Ω)|Summable (fun n=>‖C z n‖^2)}:=
    SquareSeriesField.good_measurable C hm
  have hsection (v s : ℝ) : ∀ᵐ ω ∂μ,Summable (fun n=>‖C (v,(s,ω)) n‖^2) := by
    by_cases hv : MovingMeanPhysicalField.valid H h v s
    · have hvalid:=section_summable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
        P haP h Z htarget hstop F hF hFm J hIJ₀ hIJ₁ hlocal hΛ hH hsmallPoint hsmallL2
        hages hrootStop hrootTarget hcenter hspan k hfresh hold A0 ν hA0 hν hjet χ hχ0 hχ1 p hp horder
        Bpast Babs B0 hBDGpast hBDGabs hBDG mass ρ hmass hρ hρhalf
        (Real.toNNReal v) (Real.toNNReal s)
        (by change ((Real.toNNReal v:ℝ≥0):ℝ)+(h:ℝ)≤(H:ℝ)
            simp only [Real.toNNReal_of_nonneg hv.1];exact hv.2.2.2)
        (by change (0:ℝ)<((Real.toNNReal s:ℝ≥0):ℝ)
            simpa only [Real.toNNReal_of_nonneg hv.2.1.le,NNReal.coe_mk] using hv.2.1)
        (by change ((Real.toNNReal s:ℝ≥0):ℝ)<(h:ℝ)
            simpa only [Real.toNNReal_of_nonneg hv.2.1.le,NNReal.coe_mk] using hv.2.2.1)
      simpa only [Real.toNNReal_of_nonneg hv.1,Real.toNNReal_of_nonneg hv.2.1.le,NNReal.coe_mk] using hvalid
    · exact ae_of_all _ (fun ω=>by
        have hz (x : HeatCircle) : Scalar k ((v,(s,ω)),x)=0 := by
          change Complex.ofReal (MovingComparisonField.field 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
            P haP h Z htarget hstop F hF hFm k (v,(s,(ω,x))))=0
          rw [MovingComparisonField.field_zero_of_not_valid 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
            P haP h Z htarget hstop F hF hFm k _ hv,Complex.ofReal_zero]
        have hc (n : ℤ) : C (v,(s,ω)) n=0:=by
          dsimp only [C,NativeNegativeRealization.coefficients]
          simp only [hz,fourierCoeff,smul_zero,integral_zero,mul_zero]
        simp only [hc,norm_zero,zero_pow (by decide : (2:ℕ)≠0),summable_zero])
  apply (Measure.ae_prod_iff_ae_ae hevent).mpr
  exact ae_of_all _ (fun v=>
    (Measure.ae_prod_iff_ae_ae (hevent.preimage (measurable_const.prodMk measurable_id))).mpr
      (ae_of_all _ (fun s=>hsection v s)))

end SHE.MovingComparisonSummability

