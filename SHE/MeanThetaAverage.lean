module

public import SHE.MeanDampedEnergy
public import SHE.HilbertFiniteAverage

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency true
noncomputable section

namespace SHE.MeanThetaAverage
open Set MeasureTheory Real PredictableL2 MeanRMSTimeFactors
open QuarterRMSTimeFactors (oldTimeBudget)
open scoped NNReal ENNReal
variable {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
variable [InnerProductSpace ℝ E] [CompleteSpace E]
variable [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

def thetaMeasure : Measure ℝ := volume.restrict (Ioc (0:ℝ) 1)

instance thetaMeasure_probability : IsProbabilityMeasure thetaMeasure := ⟨by simp [thetaMeasure]⟩

def average (F : ℝ×(ℝ≥0×Ω)→E) (z : ℝ≥0×Ω) : E := ∫ θ,F (θ,z) ∂thetaMeasure

/-- Interpolation is averaged as a Hilbert-valued field before the
square. Uniform dimensional witnesses allow the exact same retained
damping/current-input envelope to survive this additional integral. -/
theorem retained_current_energy (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
    (Q : CanonicalCovariance.ProfileParameters) (ell : ℝ) (Cs : ℕ→ℝ)
    (k : ℕ) (ρ T A0 ν K χ D Λ ε : ℝ) (hΛ : 0<Λ) (hρ : 0<ρ) (hρhalf : ρ<1/2)
    (hε : 0≤ε) (hερ : 2*ε<ρ) (hT : 0<T) (hν : 0≤ν)
    (hK : 0≤K) (hχ : 0≤χ) (hD : 0≤D) (V : ℝ≥0→ℝ) (hV : Measurable V)
    (hV0 : ∀ q,0≤V q) (hb : ∀ q : ℝ≥0,q≤H → (q:ℝ)<T → V q≤D)
    (F : ℝ×(ℝ≥0×Ω)→E) (hF : Measurable F)
    (hs : ∀ θ∈Ioc (0:ℝ) 1,∀ q : ℝ≥0,q≤H → (q:ℝ)<T →
      Integrable (fun ω=>‖F (θ,(q,ω))‖^2) μ ∧
      (∫ ω,‖F (θ,(q,ω))‖^2 ∂μ)≤
        (K*(T-q)^(ρ/2)*(V q)^(χ/2)*((4:ℝ)^ε*Λ^(-ε))*
          oldTimeBudget Q ell Cs k T q (1/2-ε) A0 ν)^2)
    (hz : ∀ θ∈Ioc (0:ℝ) 1,∀ q : ℝ≥0,T≤(q:ℝ) → ∀ ω,F (θ,(q,ω))=0) :
    Integrable (fun z=>‖average F z‖^2) (energyMeasure μ H) ∧
      (∫ z,‖average F z‖^2 ∂energyMeasure μ H)≤
        ∫ q,MeanBudgetEnergy.envelope Q ell Cs k (ρ-2*ε) T A0 ν
          (MeanDampedEnergy.prefactor Λ ε K) χ V q ∂timeMeasure H := by
  have hAvg : Measurable (average F) := hF.stronglyMeasurable.integral_prod_left'.measurable
  apply MeanDampedEnergy.product_bound μ H Q ell Cs k ρ T A0 ν K χ D Λ ε
    hΛ hρ hρhalf hε hερ hT hν hK hχ hD V hV hV0 hb (average F) hAvg
  · intro q hqH hqT
    let B : ℝ := K*(T-q)^(ρ/2)*(V q)^(χ/2)*((4:ℝ)^ε*Λ^(-ε))*
      oldTimeBudget Q ell Cs k T q (1/2-ε) A0 ν
    have hm : Measurable (fun z : ℝ×Ω=>F (z.1,(q,z.2))) :=
      hF.comp (measurable_fst.prodMk (measurable_const.prodMk measurable_snd))
    have hh : ∀ᵐ θ ∂thetaMeasure,Integrable (fun ω=>‖F (θ,(q,ω))‖^2) μ ∧
        (∫ ω,‖F (θ,(q,ω))‖^2 ∂μ)≤|B|^2 := by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with θ hθ
      simpa only [sq_abs] using hs θ hθ q hqH hqT
    have he := HilbertParameterAverage.energy μ thetaMeasure _ hm (fun _=>|B|)
      measurable_const (integrable_const _) (fun _=>abs_nonneg _)
      (hh.mono (fun _ h=>h.1)) (hh.mono (fun _ h=>h.2))
    refine ⟨he.2.1,?_⟩
    simpa only [integral_const,probReal_univ,one_smul,sq_abs,average] using he.2.2
  · intro q hq ω
    change (∫ θ,F (θ,(q,ω)) ∂thetaMeasure)=0
    apply integral_eq_zero_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with θ hθ
    exact hz θ hθ q hq ω

end SHE.MeanThetaAverage
