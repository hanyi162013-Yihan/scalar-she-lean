module

public import SHE.MovingMeanRootScalar
public import SHE.MovingComparisonEnergy
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

namespace SHE.MovingComparisonField
open AddCircle
open MeasureTheory PredictableL2 NativeHeatObservation NativeObservationNaturality
open FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation StoppedItoInputs
open scoped NNReal ENNReal
local instance movingComparisonField_realSigma : MeasurableSpace RealL2 := borel _
local instance movingComparisonField_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance movingComparisonField_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance movingComparisonField_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance movingComparisonField_blockSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance movingComparisonField_blockBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
variable {Ω : Type} [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
variable (Λ κ : ℝ) (hκ : 0<κ) {aU aV : ℝ→ℝ} (haU : Measurable aU) (haV : Measurable aV) {ell M : ℝ}
variable (hell : 0<ell) (hbU : ∀ z,ell≤aU z ∧ aU z≤M) (hbV : ∀ z,ell≤aV z ∧ aV z≤M)
variable (I₀ I₁ : StandardTerminalIto (C := RealHaarIntegrand.Columns) (E := RealL2) 𝓕 μ H)
variable (u₀ : RealL2)
variable (S : MixedNativeAdditiveResidualPair.Solution 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀)

local instance movingComparisonField_circleSigma : MeasurableSpace CircleL2 := borel _
local instance movingComparisonField_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩
local instance movingComparisonField_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
local instance movingComparisonField_twoFinite : Fact ((2:ℝ≥0∞)≠∞) := ⟨by simp⟩
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

local notation "MS"=>MovingMeanRootScalar.meanField 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
  P haP h Z htarget hstop F hF hFm

/-- A genuine jointly Borel scalar representative of the literal finite
reference-tree comparison, retaining its spatial root. -/
def field (k : ℕ) (z : ℝ×(ℝ×(Ω×HeatCircle))) : ℝ:=CF k z+MS k z+BF k z
local notation "Cmp"=>field 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
  P haP h Z htarget hstop F hF hFm

theorem field_measurable (hΛ : 0≤Λ)
    (hsmall : ProfileStability.memoryConstant P.lower P.holder P.exponent*
      ProfileVolterra.powerConstant ((P.exponent-2)/4)*P.horizon^(P.exponent/4)≤1/2) (k : ℕ) :
    Measurable (Cmp k) := by
  exact ((MovingMarkRootTheta.covarianceField_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S
    P P.coefficient haP h Z htarget hstop F hF hFm hΛ hsmall k).add
      (MovingMeanRootScalar.meanField_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
        P haP h Z htarget hstop F hF hFm k)).add
    (MovingMarkRootTheta.baselineField_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S
      P P.coefficient haP h Z htarget hstop F hF hFm hΛ hsmall k)

def energy (k : ℕ) (mass ρ : ℝ) (z : ℝ×(ℝ×Ω)) : ℝ:=
  NativeFourierAverage.scalarEnergy mass ρ (fun x=>Complex.ofReal (Cmp k (z.1,(z.2.1,(z.2.2,x)))))
local notation "En"=>energy 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
  P haP h Z htarget hstop F hF hFm

theorem energy_measurable (hΛ : 0≤Λ)
    (hsmall : ProfileStability.memoryConstant P.lower P.holder P.exponent*
      ProfileVolterra.powerConstant ((P.exponent-2)/4)*P.horizon^(P.exponent/4)≤1/2)
    (k : ℕ) (mass ρ : ℝ) : Measurable (En k mass ρ) := by
  have hm : Measurable (fun z : (ℝ×(ℝ×Ω))×HeatCircle=>Complex.ofReal (Cmp k (z.1.1,(z.1.2.1,(z.1.2.2,z.2))))) :=
    Complex.continuous_ofReal.measurable.comp ((field_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
      P haP h Z htarget hstop F hF hFm hΛ hsmall k).comp
        (measurable_fst.fst.prodMk (measurable_fst.snd.fst.prodMk
          (measurable_fst.snd.snd.prodMk measurable_snd))))
  exact Measurable.tsum (fun n : ℤ=>measurable_const.mul
    ((NativeFourierAverage.scalar_coefficient_measurable _ hm n).norm.pow_const 2))

theorem field_zero_of_not_valid (k : ℕ) (z : ℝ×(ℝ×(Ω×HeatCircle)))
    (hz : ¬MovingMeanPhysicalField.valid H h z.1 z.2.1) : Cmp k z=0 := by
  simp only [field,MovingMarkRootTheta.covarianceField,MovingMeanRootScalar.meanField,
    MovingMarkRootTheta.baselineField,if_neg hz,zero_add]

include hIJ₀ hIJ₁ in
/-- The Borel field is the literal arbitrary-current-time native
reference endpoint difference on each actual moving-window section. -/
theorem field_eq_endpoint_ae (hlocal : StandardTerminalPastLocality J) (hΛ : 0≤Λ)
    (hH : (H:ℝ)≤1)
    (hsmallPoint : ProfileStability.memoryConstant P.lower P.holder P.exponent*
      ProfileVolterra.powerConstant ((P.exponent-2)/4)*P.horizon^(P.exponent/4)≤1/2)
    (hsmallL2 : ProfileStability.memoryConstant P.lower P.holder P.exponent*
      ProfileVolterra.powerConstant ((P.exponent-1)/4)*P.horizon^(P.exponent/4)≤1/2)
    (hages : ∀ x i,(Z.observations x i).stop≤(Z.observations x i).target)
    (hrootStop : ∀ x i,(Z.observations x i).stop≤(h:ℝ))
    (hrootTarget : ∀ x i,(Z.observations x i).target=(h:ℝ))
    (hcenter : ∀ x,(Z.observations x 0).center=x)
    (hspan : (h:ℝ)≤P.horizon) (k : ℕ) (hfresh : (h:ℝ)≤UniformFutureProfileScores.horizon (1+k))
    (hold : ∀ j,j<k→(h:ℝ)≤uniformHorizon 1 j)
    (A0 ν : ℝ) (hA0 : 0≤A0) (hν : 0≤ν)
    (hjet : ∀ x j,j≤k→∀ z,‖iteratedFDeriv ℝ j (F x) z‖≤A0*ν^j)
    (Bpast Babs : ℝ≥0) (hBDGpast : StandardTerminalBDGPower 1 J Bpast)
    (hBDGabs : StandardTerminalBDGPower (k+2) J Babs)
    (v s : ℝ≥0) (hvH : v+h≤H) (hs : 0<s) (hsh : s<h) :
    ∀ᵐ z : Ω×HeatCircle ∂μ.prod haarAddCircle,Cmp k ((v:ℝ),((s:ℝ),z))=End k v s z := by
  have hv : MovingMeanPhysicalField.valid H h (v:ℝ) (s:ℝ):=
    ⟨v.2,by exact_mod_cast hs,by exact_mod_cast hsh,by exact_mod_cast hvH⟩
  have he:=MovingRootThreeLeg.actual_moving_transfer 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
    P haP h Z htarget hstop F hF hFm J hIJ₀ hIJ₁ hlocal hΛ hH hsmallPoint hsmallL2
    hages hrootStop hrootTarget hcenter hspan k hfresh hold A0 ν hA0 hν hjet Bpast hBDGpast Babs hBDGabs
    v s hvH hs hsh
  filter_upwards [he] with z hz
  rcases z with ⟨ω,x⟩
  simpa only [field,MovingMarkRootTheta.covarianceField,MovingMeanRootScalar.meanField,
    MovingMarkRootTheta.baselineField,if_pos hv,Real.toNNReal_coe,
    MovingMeanRootScalar.meanTheta_eq_absolute,MovingComparisonSection.endpointDifference] using hz.symm

include hIJ₀ hIJ₁ in
theorem energy_eq_endpoint_ae (hlocal : StandardTerminalPastLocality J) (hΛ : 0≤Λ)
    (hH : (H:ℝ)≤1)
    (hsmallPoint : ProfileStability.memoryConstant P.lower P.holder P.exponent*
      ProfileVolterra.powerConstant ((P.exponent-2)/4)*P.horizon^(P.exponent/4)≤1/2)
    (hsmallL2 : ProfileStability.memoryConstant P.lower P.holder P.exponent*
      ProfileVolterra.powerConstant ((P.exponent-1)/4)*P.horizon^(P.exponent/4)≤1/2)
    (hages : ∀ x i,(Z.observations x i).stop≤(Z.observations x i).target)
    (hrootStop : ∀ x i,(Z.observations x i).stop≤(h:ℝ))
    (hrootTarget : ∀ x i,(Z.observations x i).target=(h:ℝ))
    (hcenter : ∀ x,(Z.observations x 0).center=x)
    (hspan : (h:ℝ)≤P.horizon) (k : ℕ) (hfresh : (h:ℝ)≤UniformFutureProfileScores.horizon (1+k))
    (hold : ∀ j,j<k→(h:ℝ)≤uniformHorizon 1 j)
    (A0 ν : ℝ) (hA0 : 0≤A0) (hν : 0≤ν)
    (hjet : ∀ x j,j≤k→∀ z,‖iteratedFDeriv ℝ j (F x) z‖≤A0*ν^j)
    (Bpast Babs : ℝ≥0) (hBDGpast : StandardTerminalBDGPower 1 J Bpast)
    (hBDGabs : StandardTerminalBDGPower (k+2) J Babs)
    (mass ρ v s : ℝ) :
    ∀ᵐ ω ∂μ,En k mass ρ (v,(s,ω))=
      MovingComparisonEnergy.endpointEnergy 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
        P haP h Z htarget hstop F hF hFm k mass ρ v s ω := by
  by_cases hv : MovingMeanPhysicalField.valid H h v s
  · have hvH : v.toNNReal+h≤H := by exact_mod_cast (show (v.toNNReal:ℝ)+(h:ℝ)≤(H:ℝ) by rw [Real.toNNReal_of_nonneg hv.1];exact hv.2.2.2)
    have hs : (0:ℝ≥0)<s.toNNReal:=by exact_mod_cast (show (0:ℝ)<(s.toNNReal:ℝ) by rw [Real.toNNReal_of_nonneg hv.2.1.le];exact hv.2.1)
    have hsh : s.toNNReal<h:=by exact_mod_cast (show (s.toNNReal:ℝ)<(h:ℝ) by rw [Real.toNNReal_of_nonneg hv.2.1.le];exact hv.2.2.1)
    have he:=field_eq_endpoint_ae 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h Z htarget hstop F hF hFm
      J hIJ₀ hIJ₁ hlocal hΛ hH hsmallPoint hsmallL2 hages hrootStop hrootTarget hcenter hspan k hfresh hold
      A0 ν hA0 hν hjet Bpast Babs hBDGpast hBDGabs v.toNNReal s.toNNReal hvH hs hsh
    simp only [Real.toNNReal_of_nonneg hv.1,Real.toNNReal_of_nonneg hv.2.1.le,NNReal.coe_mk] at he
    filter_upwards [Measure.ae_ae_of_ae_prod he] with ω hω
    unfold energy MovingComparisonEnergy.endpointEnergy
    rw [if_pos hv]
    unfold NativeFourierAverage.scalarEnergy
    apply tsum_congr
    intro n
    have hc:=congrFun (fourierCoeff_congr_ae (hω.mono (fun x hx=>congrArg Complex.ofReal hx))) n
    rw [hc]
    simp only [Real.toNNReal_of_nonneg hv.1,Real.toNNReal_of_nonneg hv.2.1.le]
  · exact ae_of_all _ (fun ω=>by
      have hz (x : HeatCircle) : Cmp k (v,(s,(ω,x)))=0:=
        field_zero_of_not_valid 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
          P haP h Z htarget hstop F hF hFm k (v,(s,(ω,x))) hv
      simp [energy,MovingComparisonEnergy.endpointEnergy,if_neg hv,hz,
        NativeFourierAverage.scalarEnergy,fourierCoeff])

end SHE.MovingComparisonField

