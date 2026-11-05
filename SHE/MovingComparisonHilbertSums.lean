module

public import SHE.MovingComparisonRootSums
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

namespace SHE.MovingComparisonHilbertSums
open RootSmoothSums
open AddCircle
open MeasureTheory PredictableL2 NativeHeatObservation NativeObservationNaturality
open FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation StoppedItoInputs
open scoped NNReal ENNReal
local instance movingComparisonHilbertSums_realSigma : MeasurableSpace RealL2 := borel _
local instance movingComparisonHilbertSums_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance movingComparisonHilbertSums_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance movingComparisonHilbertSums_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance movingComparisonHilbertSums_blockSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance movingComparisonHilbertSums_blockBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
variable {Ω : Type} [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
variable (Λ κ : ℝ) (hκ : 0<κ) {aU aV : ℝ→ℝ} (haU : Measurable aU) (haV : Measurable aV) {ell M : ℝ}
variable (hell : 0<ell) (hbU : ∀ z,ell≤aU z ∧ aU z≤M) (hbV : ∀ z,ell≤aV z ∧ aV z≤M)
variable (I₀ I₁ : StandardTerminalIto (C := RealHaarIntegrand.Columns) (E := RealL2) 𝓕 μ H)
variable (u₀ : RealL2)
variable (S : MixedNativeAdditiveResidualPair.Solution 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀)

local instance movingComparisonHilbertSums_circleSigma : MeasurableSpace CircleL2 := borel _
local instance movingComparisonHilbertSums_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩
local instance movingComparisonHilbertSums_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
local instance movingComparisonHilbertSums_twoFinite : Fact ((2:ℝ≥0∞)≠∞) := ⟨by simp⟩
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
theorem section_sum_ae (hlocal : StandardTerminalPastLocality J) (hΛ : 0<Λ)
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
    (mass ρ : ℝ) (hmass : 1≤mass) (hρ : 0<ρ) (hρhalf : ρ<1/2)
    (v s : ℝ≥0) (hvH : v+h≤H) (hs : 0<s) (hsh : s<h) (a : Finset ℕ) :
    (fun ω=>Out (rootSum F a) (rootSum_uniform F hF a) (rootSum_measurable F hFm a) k mass ρ
      ((v:ℝ),((s:ℝ),ω)))=ᵐ[μ]
      fun ω=>∑ j∈a,Out (F j) (hF j) (hFm j) k mass ρ ((v:ℝ),((s:ℝ),ω)) := by
  have hc (G : HeatCircle→WordRecursion.State 1→ℝ) (hg : UniformBoundedSmooth G)
      (hgm : Measurable (fun z : HeatCircle×WordRecursion.State 1=>G z.1 z.2)) :
      ∀ᵐ ω ∂μ,∀ n : ℤ,
        fourierCoeff (Out G hg hgm k mass ρ ((v:ℝ),((s:ℝ),ω))) n=
          NativeNegativeRealization.coefficients mass ρ (Raw G hg hgm k) ((v:ℝ),((s:ℝ),ω)) n := by
    obtain ⟨A,hA,hjet⟩:=hg.finite_jet_bound k
    have hh:=MovingComparisonSummability.section_summable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
      P haP h Z htarget hstop G hg hgm J hIJ₀ hIJ₁ hlocal hΛ hH hsmallPoint hsmallL2
      hages hrootStop hrootTarget hcenter hspan k hfresh hold A 1 hA (by norm_num) hjet
      χ hχ0 hχ1 p hp horder Bpast Babs B0 hBDGpast hBDGabs hBDG mass ρ hmass hρ hρhalf v s hvH hs hsh
    filter_upwards [hh] with ω hω
    intro n
    exact NativeNegativeRealization.value_fourier mass ρ hmass _ _
      (hω.congr (fun j=>NativeNegativeRealization.coefficients_norm_sq mass ρ hmass _ _ j)) n
  have hscalar:=MovingComparisonRootSums.section_sum_ae 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
    P haP h Z htarget hstop F hF hFm J hIJ₀ hIJ₁ hlocal hΛ.le hH hsmallPoint hsmallL2
    hages hrootStop hrootTarget hcenter hspan k hfresh hold Bpast Babs hBDGpast hBDGabs v s hvH hs hsh a
  have hi (j : ℕ):=MovingComparisonRootSums.section_integrable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
    P haP h Z htarget hstop F hF hFm J hIJ₀ hIJ₁ hlocal hΛ.le hH hsmallPoint hsmallL2
    hages hrootStop hrootTarget hcenter hspan k hfresh hold Bpast Babs hBDGpast hBDGabs v s hvH hs hsh j
  filter_upwards [hc (rootSum F a) (rootSum_uniform F hF a) (rootSum_measurable F hFm a),
    ae_all_iff.2 (fun j=>hc (F j) (hF j) (hFm j)),Measure.ae_ae_of_ae_prod hscalar,
    ae_all_iff.2 (fun j=>(hi j).prod_right_ae)] with ω hcut hband hsum hint
  apply (_root_.fourierBasis (T:=2*Real.pi)).repr.injective
  apply lp.ext
  funext n
  rw [map_sum,lp.coeFn_sum,Finset.sum_apply]
  simp only [fourierBasis_repr,hcut,hband]
  have hraw : (fun x=>Raw (rootSum F a) (rootSum_uniform F hF a) (rootSum_measurable F hFm a)
      k (((v:ℝ),((s:ℝ),ω)),x))=ᵐ[haarAddCircle]
      fun x=>∑ j∈a,Raw (F j) (hF j) (hFm j) k (((v:ℝ),((s:ℝ),ω)),x) := by
    filter_upwards [hsum] with x hx
    change Complex.ofReal (_)=∑ j∈a,Complex.ofReal (_)
    rw [hx,Complex.ofReal_sum]
  have hcoef:=congrFun (fourierCoeff_congr_ae hraw) n
  have hfinite:=congrFun (fourierCoeff.sum a
    (fun j x=>Raw (F j) (hF j) (hFm j) k (((v:ℝ),((s:ℝ),ω)),x))
      (fun j _=>Complex.ofRealCLM.integrable_comp (hint j))) n
  have hfun : (∑ j∈a,(fun x=>Raw (F j) (hF j) (hFm j) k (((v:ℝ),((s:ℝ),ω)),x)))=
      (fun x=>∑ j∈a,Raw (F j) (hF j) (hFm j) k (((v:ℝ),((s:ℝ),ω)),x)) := by
    ext x
    simp only [Finset.sum_apply]
  rw [hfun] at hfinite
  simp only [Finset.sum_apply] at hfinite
  unfold NativeNegativeRealization.coefficients
  rw [hcoef,hfinite]
  simp only [Finset.sum_apply,Finset.mul_sum]

end SHE.MovingComparisonHilbertSums
