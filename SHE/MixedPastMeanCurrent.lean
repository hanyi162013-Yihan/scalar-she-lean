module

public import SHE.MixedPastSpatialMoments
public import SHE.ControlledFamilyMeanFields
public import SHE.MixedPastKernelSections
public import SHE.ControlledFamilyMeanEnergy
public import SHE.MixedPastMeanInputEnergy
public import SHE.NativeKernelReindex
public import SHE.MixedPastMeanAverage
public import SHE.MixedPastMeanTimeFields
public import SHE.PastMeanThetaEnergy
public import SHE.MeanCurrentFields

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3600000
set_option quotPrecheck false

namespace SHE.MixedPastMeanCurrent
open MeasureTheory PredictableL2 NativeHeatObservation NativeObservationNaturality
  FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation StoppedItoInputs
open scoped NNReal ENNReal
local instance mixedPastMeanCurrent_realSigma : MeasurableSpace RealL2 := borel _
local instance mixedPastMeanCurrent_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance mixedPastMeanCurrent_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance mixedPastMeanCurrent_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance mixedPastMeanCurrent_blockSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance mixedPastMeanCurrent_blockBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
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
open Real AddCircle Set Filter WordRecursion ControlledProfile ControlledReferenceLevel SmoothCylinders UniformSmooth
  CutoffWordLevel CutoffWordHistories CutoffCarriers PhysicalScoreChain PhysicalChainArrays
  PhysicalParentGeometry CoveredHistoryGeometry CoveredControlledLaw ControlledOldIntervals
  HistoryProductMeasure ActualMeanKernel
local instance mixedPastMeanCurrent_circleSigma : MeasurableSpace CircleL2 := borel _
local instance mixedPastMeanCurrent_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩
local instance mixedPastMeanCurrent_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
local instance mixedPastMeanCurrent_secondCountable : SecondCountableTopology CircleL2 :=
  (_root_.fourierBasis (T:=2*Real.pi)).repr.toHomeomorph.secondCountableTopology
variable (P : CanonicalCovariance.ProfileParameters) (haP : BoundedSmooth P.coefficient)
variable (v b : ℝ≥0) (hvb : v≤b)
variable (Z : VariableObservations.Family HeatCircle 1)
variable (htarget : ∀ x i,(b:ℝ)≤(Z.observations x i).target)
variable (hstop : ∀ x i,(b:ℝ)≤(Z.observations x i).stop)
variable (F : HeatCircle→WordRecursion.State 1→ℝ) (hF : UniformBoundedSmooth F)
variable (hFm : Measurable (fun z : HeatCircle×WordRecursion.State 1=>F z.1 z.2))
local notation "Base" => ControlledReferenceThetaGeometry.level P P.coefficient haP Λ v b hvb Z htarget hstop F hF hFm
local notation "Zero" => Base (0,(0,0))
local notation "U" => MixedPastJointData.pastU 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S v
local notation "Dir" => MixedPastJointData.pastD 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S v
local notation "Mean" => MixedPastLiteralPoint.meanField 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S P haP v b hvb Z htarget hstop F hF hFm
open NativeRandomKernel NormalizedKernelSplit QuarterSpatialEvent
local notation "Input" => MixedPastMeanInputEnergy.input 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP v b hvb Z htarget hstop F hF hFm
attribute [local irreducible] MixedPastLiteralPoint.meanField MixedPastJointData.pastU MixedPastJointData.pastD

local notation "Average" => MixedPastMeanFields.average 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
  P haP v b hvb Z htarget hstop F hF hFm

/-- Original local-current window, with old times integrated first. -/
def field (k : ℕ) (old : Measure (Fin k→ℝ))
    (mass ρ : ℝ) (hmass : 1≤mass) (hρ : 0≤ρ) (z : ℝ×(ℝ≥0×Ω)) : CircleL2 :=
  if v<z.2.1 ∧ z.2.1<b then Average k old z.1 z.2.1 mass ρ hmass hρ z.2.2 else 0

def value (k : ℕ) (old : Measure (Fin k→ℝ))
    (mass ρ : ℝ) (hmass : 1≤mass) (hρ : 0≤ρ) (z : ℝ≥0×Ω) : CircleL2 :=
  MeanThetaAverage.average (field 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
    P haP v b hvb Z htarget hstop F hF hFm k old mass ρ hmass hρ) z

theorem field_measurable (hΛ : 0≤Λ) (k : ℕ) (old : Measure (Fin k→ℝ)) [SFinite old]
    (mass ρ : ℝ) (hmass : 1≤mass) (hρ : 0≤ρ) :
    Measurable (field 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
      P haP v b hvb Z htarget hstop F hF hFm k old mass ρ hmass hρ) := by
  have hh:=MixedPastMeanTimeFields.average_time_joint_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
    P haP v b hvb Z htarget hstop F hF hFm hΛ k old mass ρ hmass hρ
  have hq : Measurable (fun z : ℝ×(ℝ≥0×Ω)=>(z.2.1:ℝ)):=
    measurable_subtype_coe.comp measurable_snd.fst
  exact hh.ite ((measurableSet_lt measurable_const hq).inter
    (measurableSet_lt hq measurable_const)) measurable_const

include hIJ₀ hIJ₁ in
/-- The literal random-past mean input has finite current-time/sample
energy after BOTH old times and interpolation are averaged before the
square. The exact original current difference energy is retained, with
the proved damping power and genuine local relative-age assignment budget. -/
theorem actual_current_energy (hlocal : StandardTerminalPastLocality J) (hΛ : 0<Λ)
    (hvbstrict : v<b) (hb1 : (b:ℝ)≤1)
    (hages : ∀ x i,(Z.observations x i).stop≤(Z.observations x i).target)
    (hrootStop : ∀ x i,(Z.observations x i).stop≤(b:ℝ))
    (hrootTarget : ∀ x i,(Z.observations x i).target=(b:ℝ))
    (hcenter : ∀ x,(Z.observations x 0).center=x)
    (hspan : (b:ℝ)-(v:ℝ)≤P.horizon) (k : ℕ)
    (hfresh : (b:ℝ)-(v:ℝ)≤UniformFutureProfileScores.horizon (1+k))
    (hold : ∀ j,j<k→(b:ℝ)-(v:ℝ)≤uniformHorizon 1 j)
    (A0 ν : ℝ) (hA0 : 0≤A0) (hν : 0≤ν)
    (hjet : ∀ x j,j≤k→∀ z,‖iteratedFDeriv ℝ j (F x) z‖≤A0*ν^j)
    (χ : ℝ) (hχ0 : 0≤χ) (hχ1 : χ<1) (p : ℕ) (hp : 0<p) (horder : 1≤(p:ℝ)*(1-χ))
    (B0 : ℝ≥0) (hBDG : StandardTerminalBDGPower ((2*p)*(k+2)) J B0)
    (mass ρ : ℝ) (hmass : 1≤mass) (hρ : 0<ρ) (hρhalf : ρ<1/2)
    (ε : ℝ) (hε : 0≤ε) (hερ : 2*ε<ρ) :
    let N:=(2*p)*(k+2)
    let CG:=MixedPastWordMoments.momentConstant P k k (2*p)
      ((k:ℝ)*(NativeHybridMoments.momentConstant N B0 κ M)^P.exponent)
    let CD:=MixedHeatedDifferenceMoments.momentConstant N B0 κ M^((1-χ)/(k+2:ℝ))
    let C:=((CD+CG)/2)^(1/(p:ℝ))
    let K:=PastMeanRMS.coefficient P k ρ C*((4:ℝ)^ε*Λ^(-ε))
    let E:=fun q : ℝ≥0=>∫ ω,‖S.second q ω-S.first q ω‖^2 ∂μ
    let old : Measure (Fin k→ℝ):=Measure.pi (fun _=>volume.restrict (Ioc (v:ℝ) (b:ℝ)))
    let V : ℝ≥0×Ω→CircleL2:=value 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
      P haP v b hvb Z htarget hstop F hF hFm k old mass ρ hmass hρ.le
    Integrable (fun z=>‖V z‖^2) (energyMeasure μ H) ∧
      (∫ z,‖V z‖^2 ∂energyMeasure μ H)≤
        ∫ q,PastMeanTimeFactors.energyEnvelope P (fraction P*P.lower) (uniformConstant 1)
          k ρ v b (1/2-ε) A0 ν K χ E q ∂timeMeasure H := by
  intro N CG CD C K E old V
  let D:=MixedHeatedDifferenceMoments.momentConstant N B0 κ M^(1/(N:ℝ))
  have hN : 0<N:=Nat.mul_pos (Nat.mul_pos (by norm_num) hp) (by omega)
  have hD : 0≤D:=rpow_nonneg (MixedHeatedDifferenceMoments.momentConstant_nonneg (κ:=κ)
    hκ.le (hell.le.trans ((hbU 0).1.trans (hbU 0).2)) N B0) _
  have hE : Measurable E:=ActualInterpolatedMeanFields.current_energy_measurable
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S
  have hE0 (q : ℝ≥0) : 0≤E q:=integral_nonneg (fun _=>sq_nonneg _)
  have hEb (q : ℝ≥0) (hqH : q≤H) (_ : (v:ℝ)<q) (hqb : (q:ℝ)<b) : E q≤D:=
    (MixedHeatedDifferenceMoments.current_energy 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
      J hIJ₀ hIJ₁ hΛ.le q hqH (hqb.le.trans hb1) N hN B0 hBDG).2
  have hK : 0≤K:=mul_nonneg (PastMeanRMS.coefficient_nonneg P k ρ C)
    (mul_nonneg (rpow_nonneg (by norm_num) ε) (rpow_nonneg hΛ.le (-ε)))
  let G : ℝ×(ℝ≥0×Ω)→CircleL2:=field 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
    P haP v b hvb Z htarget hstop F hF hFm k old mass ρ hmass hρ.le
  have hG : Measurable G:=field_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
    P haP v b hvb Z htarget hstop F hF hFm hΛ.le k old mass ρ hmass hρ.le
  apply PastMeanTimeFactors.theta_energy_product_bound μ H P (fraction P*P.lower) (uniformConstant 1)
    k ρ v b (1/2-ε) A0 ν K χ D hρ (by linarith) (by exact_mod_cast hvbstrict)
      hν hK hχ0 hD E hE hE0 hEb G hG
  · intro θ hθ q hqH hvq hqb
    have ha : v<q ∧ q<b:=⟨by exact_mod_cast hvq,by exact_mod_cast hqb⟩
    have htθ : |θ|≤1:=by rw [abs_of_nonneg hθ.1.le];exact hθ.2
    have hh:=MixedPastMeanAverage.actual_averaged_energy 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
      J hIJ₀ hIJ₁ P haP v b hvb Z htarget hstop F hF hFm hlocal hΛ hages hrootStop hrootTarget hcenter
      hspan k hfresh hold θ htθ A0 ν hA0 hν hjet χ hχ0 hχ1 p hp horder B0 hBDG mass ρ hmass hρ hρhalf
      ε hε (by linarith) q (le_of_lt ha.1) ha.2 hqH (hqb.le.trans hb1)
    have hraw : (fun ω=>G (θ,(q,ω)))=fun ω=>Average k old θ q mass ρ hmass hρ.le ω := by
      funext ω
      exact if_pos ha
    have heval (ω : Ω):=congrFun hraw ω
    simp_rw [heval]
    refine ⟨hh.2.1,?_⟩
    have heq :
        (PastMeanRMS.coefficient P k ρ C*((b:ℝ)-q)^(ρ/2)*(E q)^(χ/2)*((4:ℝ)^ε*Λ^(-ε))*
          QuarterRMSTimeFactors.oldTimeBudget P (fraction P*P.lower) (uniformConstant 1)
            k ((b:ℝ)-v) ((q:ℝ)-v) (1/2-ε) A0 ν)^2=
        (K*(E q)^(χ/2)*((b:ℝ)-q)^(ρ/2)*
          QuarterRMSTimeFactors.oldTimeBudget P (fraction P*P.lower) (uniformConstant 1)
            k ((b:ℝ)-v) ((q:ℝ)-v) (1/2-ε) A0 ν)^2 := by
      dsimp only [K]
      ring
    exact hh.2.2.trans_eq heq
  · intro θ hθ q hq ω
    have ha : ¬(v<q ∧ q<b):=by intro ha;exact hq ⟨by exact_mod_cast ha.1,by exact_mod_cast ha.2⟩
    exact if_neg ha

end SHE.MixedPastMeanCurrent
