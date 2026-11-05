module

public import SHE.FullResidualPointMoments
public import SHE.FullResidualScoreDensity

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3500000
noncomputable section

namespace SHE.FullResidualWeightedPointMoments
open Set Filter MeasureTheory ProbabilityTheory Real AddCircle StoppedFourier WordRecursion
  CutoffWordLevel CutoffWordHistories CutoffCarriers GaussianCoordinates ProjectedUncutWord PhysicalScoreChain
  PhysicalChainArrays OldIntervalCovariance StoppedGaussianFeatures GaussianConvolution GaussianAssignmentBlocks
  ProfileL2 CoveredHistoryGeometry CoveredControlledLaw PhysicalParentGeometry ControlledOldIntervals
open scoped BigOperators NNReal
local instance fullResidualWeightedPointMoments_periodPositive : Fact (0<2*π) := ⟨by positivity⟩
variable {Ω X : Type} [MeasurableSpace Ω] [MeasurableSpace X]
variable (μ : Measure Ω) [IsProbabilityMeasure μ]
variable (P : CanonicalCovariance.ProfileParameters) (ha : SmoothCylinders.BoundedSmooth P.coefficient)
variable (Λ : ℝ) (u dir : CircleL2) (θ : ℝ)
variable (L : CutoffWordLevel.Level (ControlledWordLevel.referenceData P ha Λ u dir θ) X 1)

/-- Literal stop-weighted q-law/r-row point moments. The root and every
rough block retain their sharp old-gap scale. The full remaining
covariance supplies the fresh score, and the SAME original stops supply
its damping weights. Initial covered-stop applicability is explicit. -/
theorem weighted_point_even_moment_ae (hΛ : 0≤Λ)
    (hages : ∀ p i,(L.observations.observations p i).stop≤(L.observations.observations p i).target)
    (hstop : ∀ p i,(L.observations.observations p i).stop≤L.terminal p)
    (ρ : Measure X) [IsFiniteMeasure ρ] (k : ℕ) :
    ∃ Hf Cf : ℝ,0<Hf ∧ 0<Cf ∧
    ∀ᵐ p ∂CutoffWordHistories.historyMeasure (ControlledWordLevel.referenceData P ha Λ u dir θ) ρ k,
      ∀ q : ℝ≥0,(q:ℝ)<(carrier L k).terminal p → StrictHistory L k p →
      ∀ r : ℝ,(q:ℝ)≤r → r<(carrier L k).terminal p →
      (∀ i,((carrier L k).observations.observations p i).target-r≤Hf) →
      ∀ᵐ y : HeatCircle ∂haarAddCircle,
      ∀ mean : Ω→WordRecursion.State (1+k),Measurable mean →
      ∀ A0 ν : ℝ,0≤A0 → 0≤ν →
      (∀ j,j≤k → ∀ z,‖iteratedFDeriv ℝ j (L.test (rootParameter k p)) z‖≤A0*ν^j) →
      ∀ b : ℕ,0<b → ∀ C0 : ℝ,0≤C0 →
      (∀ j : Fin k,Integrable (fun ω=>|mean ω (leafIndex k (fun i=>i) j)-ControlledProfile.mean Λ u dir
          (θ,(targets L k p (leafIndex k (fun i=>i) j),centers L k p (leafIndex k (fun i=>i) j)))|^
          (((2*(b*(k+2)):ℕ):ℝ)*P.exponent)) μ ∧
        (∫ ω,|mean ω (leafIndex k (fun i=>i) j)-ControlledProfile.mean Λ u dir
          (θ,(targets L k p (leafIndex k (fun i=>i) j),centers L k p (leafIndex k (fun i=>i) j)))|^
          (((2*(b*(k+2)):ℕ):ℝ)*P.exponent) ∂μ)≤
          C0*(targets L k p (leafIndex k (fun i=>i) j))^((b*(k+2):ℕ)*P.exponent/2)) →
      let F := fun ω=>ActualMeanKernel.weightedPoint L k Λ q r (fun _=>mean ω) p y
      let c := referenceProfile P Λ u dir
      Integrable (fun ω=>|F ω|^(2*b)) μ ∧ (∫ ω,|F ω|^(2*b) ∂μ)≤
        FullResidualPointMoments.momentConstant P k b C0*
          (sqrt (2*Cf/(P.lower*((carrier L k).terminal p-r)))*
            SharpWordTimeScale.total L P k p q A0 ν*
              ScalarMeanEnvelope.globalDensity L c k p r y)^(2*b) := by
  let c := referenceProfile P Λ u dir
  have hcb (z : Domain) : fraction P*P.lower≤c z ∧
      c z≤(ControlledWordLevel.referenceData P ha Λ u dir θ).reference z :=
    ⟨(referenceProfile_bounds P Λ u dir z).1,
      (referenceProfile_bounds P Λ u dir z).2.trans ((half_le_self P.lower_pos.le).trans
        (ControlledProfile.profile_bounds P Λ u dir (θ,z)).1)⟩
  obtain ⟨Hf,Cf,hHf,hCf,henv⟩ :=
    ScalarMeanEnvelope.weighted_full_score_density_ae P ha Λ u dir θ L hΛ hages hstop ρ k
  refine ⟨Hf,Cf,hHf,hCf,?_⟩
  filter_upwards [FullResidualPointMoments.directional_even_moment_ae μ P ha Λ u dir θ L hages ρ k,
    henv,actual_scoreProduct_nonneg_ae L c (referenceProfile_measurable P Λ u dir)
      (mul_pos (fraction_pos P) P.lower_pos) hcb hages ρ k] with p hm hp hn
  intro q hq hstrict r hqr hr hsmall
  filter_upwards [hp q.2 hqr hr hsmall] with y hy
  intro mean hmean A0 ν hA0 hν hjet b hb0 C0 hC0 hoffset
  let E := StopWeightedRows.weightedHeatRow Λ ((carrier L k).observations.observations p) q r y
  have hh := hm q hq hstrict E hy.1 mean hmean A0 ν hA0 hν hjet b hb0 C0 hC0 hoffset
  let G := fun ω=>fderiv ℝ (gaussianAverage
    (WordRecursion.covariance (ControlledWordLevel.referenceData P ha Λ u dir θ).reference
      ((carrier L k).observations.observations p) q ((carrier L k).terminal p))
      (UncutSmoothWords.test L k p)) (mean ω) E
  have he (ω : Ω) : |ActualMeanKernel.weightedPoint L k Λ q r (fun _=>mean ω) p y|^(2*b)=|G ω|^(2*b) :=
    congrArg (fun z : ℝ=>|z|^(2*b)) (ActualMeanKernel.weightedPoint_of_active L k Λ q r (fun _=>mean ω) p y hq hr)
  let score := FullResidualPhysicalMoments.scoreScale P ha Λ u dir θ L k p q E
  let T := SharpWordTimeScale.total L P k p q A0 ν
  have hT : 0≤T := SharpWordTimeScale.total_nonneg L P k p q A0 ν
  have hs : 0≤score := mul_nonneg (sqrt_nonneg _) hn
  have hmul : |score| *T≤sqrt (2*Cf/(P.lower*((carrier L k).terminal p-r)))*
      T*ScalarMeanEnvelope.globalDensity L c k p r y := by
    rw [abs_of_nonneg hs]
    convert! mul_le_mul_of_nonneg_right hy.2 hT using 1 <;> ac_rfl
  have hpow := pow_le_pow_left₀ (mul_nonneg (abs_nonneg score) hT) hmul (2*b)
  have hbound := hh.2.trans (mul_le_mul_of_nonneg_left hpow
    (FullResidualPointMoments.momentConstant_nonneg P k b C0))
  exact ⟨hh.1.congr (ae_of_all _ (fun ω=>(he ω).symm)),
    (integral_congr_ae (ae_of_all _ he)).trans_le hbound⟩

end SHE.FullResidualWeightedPointMoments
