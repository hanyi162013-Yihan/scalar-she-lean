module

public import SHE.PastMeanBudgetEnergy
public import SHE.MeanThetaAverage

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 2300000
set_option backward.isDefEq.respectTransparency true
noncomputable section

namespace SHE.PastMeanTimeFactors
open Set MeasureTheory Real PredictableL2
open scoped ENNReal NNReal
variable {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
variable [InnerProductSpace ℝ E] [CompleteSpace E]
variable [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

/-- Interpolation and old times are both averaged as Hilbert vectors
before squaring. The local-window budget and the actual dependent
current-input energy survive unchanged. -/
theorem theta_energy_product_bound (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
    (P : CanonicalCovariance.ProfileParameters) (ell : ℝ) (Cs : ℕ→ℝ)
    (k : ℕ) (ρ base T fresh A0 ν K χ D : ℝ) (hρ : 0<ρ) (hdegree : 0<ρ+2*fresh-1)
    (hT : base<T) (hν : 0≤ν) (hK : 0≤K) (hχ : 0≤χ) (hD : 0≤D)
    (V : ℝ≥0→ℝ) (hV : Measurable V) (hV0 : ∀ q,0≤V q)
    (hb : ∀ q : ℝ≥0,q≤H → base<(q:ℝ) → (q:ℝ)<T → V q≤D)
    (F : ℝ×(ℝ≥0×Ω)→E) (hF : Measurable F)
    (hs : ∀ θ∈Ioc (0:ℝ) 1,∀ q : ℝ≥0,q≤H → base<(q:ℝ) → (q:ℝ)<T →
      Integrable (fun ω=>‖F (θ,(q,ω))‖^2) μ ∧
        (∫ ω,‖F (θ,(q,ω))‖^2 ∂μ)≤
          (K*(V q)^(χ/2)*(T-q)^(ρ/2)*
            QuarterRMSTimeFactors.oldTimeBudget P ell Cs k (T-base) (q-base) fresh A0 ν)^2)
    (hz : ∀ θ∈Ioc (0:ℝ) 1,∀ q : ℝ≥0,¬(base<(q:ℝ) ∧ (q:ℝ)<T) → ∀ ω,F (θ,(q,ω))=0) :
    Integrable (fun z=>‖MeanThetaAverage.average F z‖^2) (energyMeasure μ H) ∧
      (∫ z,‖MeanThetaAverage.average F z‖^2 ∂energyMeasure μ H)≤
        ∫ q,energyEnvelope P ell Cs k ρ base T fresh A0 ν K χ V q ∂timeMeasure H := by
  have hAvg : Measurable (MeanThetaAverage.average F):=
    hF.stronglyMeasurable.integral_prod_left'.measurable
  apply energy_product_bound μ H P ell Cs k ρ base T fresh A0 ν K χ D
    hρ hdegree hT hν hK hχ hD V hV hV0 hb (MeanThetaAverage.average F) hAvg
  · intro q hqH hqbase hqT
    let B:=K*(V q)^(χ/2)*(T-q)^(ρ/2)*
      QuarterRMSTimeFactors.oldTimeBudget P ell Cs k (T-base) (q-base) fresh A0 ν
    have hm : Measurable (fun z : ℝ×Ω=>F (z.1,(q,z.2))):=
      hF.comp (measurable_fst.prodMk (measurable_const.prodMk measurable_snd))
    have hh : ∀ᵐ θ ∂MeanThetaAverage.thetaMeasure,Integrable (fun ω=>‖F (θ,(q,ω))‖^2) μ ∧
        (∫ ω,‖F (θ,(q,ω))‖^2 ∂μ)≤|B|^2 := by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with θ hθ
      simpa only [sq_abs] using hs θ hθ q hqH hqbase hqT
    have he:=HilbertParameterAverage.energy μ MeanThetaAverage.thetaMeasure _ hm (fun _=>|B|)
      measurable_const (integrable_const _) (fun _=>abs_nonneg _)
      (hh.mono (fun _ h=>h.1)) (hh.mono (fun _ h=>h.2))
    refine ⟨he.2.1,?_⟩
    simpa only [integral_const,probReal_univ,one_smul,sq_abs,MeanThetaAverage.average] using he.2.2
  · intro q hq ω
    apply integral_eq_zero_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with θ hθ
    exact hz θ hθ q hq ω

end SHE.PastMeanTimeFactors
