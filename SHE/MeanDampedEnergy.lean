module

public import SHE.MeanFreshBudget
public import SHE.MeanBudgetEnergy

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHE.MeanDampedEnergy
open Set MeasureTheory Real PredictableL2 PhysicalAssignmentGapScale MeanRMSTimeFactors
open QuarterRMSTimeFactors (oldTimeBudget)
open scoped ENNReal NNReal
variable {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
variable [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

def prefactor (Λ ε K : ℝ) : ℝ := K*(4:ℝ)^ε*Λ^(-ε)/(1-2*ε)

theorem prefactor_nonneg {Λ ε K : ℝ} (hΛ : 0<Λ) (hε : ε<1/2) (hK : 0≤K) :
    0≤prefactor Λ ε K :=
  div_nonneg (mul_nonneg (mul_nonneg hK (rpow_nonneg (by norm_num) _)) (rpow_nonneg hΛ.le _)) (by linarith)

/-- The retained quarter-row damping gives an actual current-time
energy bound with an explicit mass gain. The fresh degree loss is
strictly less than half the available negative-output degree. -/
theorem product_bound (μ : Measure Ω) [SFinite μ] (H : ℝ≥0)
    (Q : CanonicalCovariance.ProfileParameters) (ell : ℝ) (Cs : ℕ→ℝ)
    (k : ℕ) (ρ T A0 ν K χ D Λ ε : ℝ) (hΛ : 0<Λ) (hρ : 0<ρ) (hρhalf : ρ<1/2)
    (hε : 0≤ε) (hερ : 2*ε<ρ) (hT : 0<T) (hν : 0≤ν)
    (hK : 0≤K) (hχ : 0≤χ) (hD : 0≤D) (V : ℝ≥0→ℝ) (hV : Measurable V)
    (hV0 : ∀ q,0≤V q) (hb : ∀ q : ℝ≥0,q≤H → (q:ℝ)<T → V q≤D)
    (F : ℝ≥0×Ω→E) (hF : Measurable F)
    (hs : ∀ q : ℝ≥0,q≤H → (q:ℝ)<T →
      Integrable (fun ω => ‖F (q,ω)‖^2) μ ∧
      (∫ ω,‖F (q,ω)‖^2 ∂μ)≤
        (K*(T-q)^(ρ/2)*(V q)^(χ/2)*((4:ℝ)^ε*Λ^(-ε))*
          oldTimeBudget Q ell Cs k T q (1/2-ε) A0 ν)^2)
    (hz : ∀ q : ℝ≥0,T≤(q:ℝ) → ∀ ω,F (q,ω)=0) :
    Integrable (fun z => ‖F z‖^2) (energyMeasure μ H) ∧
      (∫ z,‖F z‖^2 ∂energyMeasure μ H)≤
        ∫ q,MeanBudgetEnergy.envelope Q ell Cs k (ρ-2*ε) T A0 ν (prefactor Λ ε K) χ V q ∂timeMeasure H := by
  have hf : 0<(1/2:ℝ)-ε := by linarith
  apply MeanBudgetEnergy.product_bound μ H Q ell Cs k (ρ-2*ε) T A0 ν (prefactor Λ ε K) χ D
    (by linarith) hT hν (prefactor_nonneg hΛ (by linarith) hK) hχ hD V hV hV0 hb F hF
  · intro q hqH hqT
    have hp := hs q hqH hqT
    refine ⟨hp.1,?_⟩
    have he := budget_fresh_scale Q ell Cs k ρ T (1/2-ε) A0 ν hf.ne'
      (sub_pos.mpr hqT)
    have hdegree : ρ+2*((1/2:ℝ)-ε)-1=ρ-2*ε := by ring
    simp only [hdegree,show T-(T-(q:ℝ))=(q:ℝ) by ring] at he
    have hfac : K*(T-q)^(ρ/2)*(V q)^(χ/2)*((4:ℝ)^ε*Λ^(-ε))*
        oldTimeBudget Q ell Cs k T q (1/2-ε) A0 ν=
      prefactor Λ ε K*(T-q)^((ρ-2*ε)/2)*(V q)^(χ/2)*
        oldTimeBudget Q ell Cs k T q (1/2:ℝ) A0 ν := by
      calc
        _=(K*(V q)^(χ/2)*((4:ℝ)^ε*Λ^(-ε)))*
          ((T-q)^(ρ/2)*oldTimeBudget Q ell Cs k T q (1/2-ε) A0 ν) := by ring
        _=_ := by
          rw [he,show 2*((1/2:ℝ)-ε)=1-2*ε by ring]
          unfold prefactor
          ring
    have hbound := hp.2
    rwa [hfac] at hbound
  · exact hz

/-- The exact final integrand displays the squared damping gain;
neither the current input energy nor the assignment budget is replaced
by a constant in the quantitative estimate. -/
theorem envelope_power (Q : CanonicalCovariance.ProfileParameters) (ell : ℝ) (Cs : ℕ→ℝ)
    (k : ℕ) (ρ T A0 ν K χ Λ ε : ℝ) (hΛ : 0<Λ)
    (V : ℝ≥0→ℝ) (hV : ∀ q,0≤V q) (q : ℝ≥0) :
    MeanBudgetEnergy.envelope Q ell Cs k (ρ-2*ε) T A0 ν (prefactor Λ ε K) χ V q=
      Λ^(-2*ε)*(K*(4:ℝ)^ε/(1-2*ε))^2*(V q)^χ*
        currentBudget Q ell Cs k (ρ-2*ε) T A0 ν q^2 := by
  have hp : (Λ^(-ε))^2=Λ^(-2*ε) := by
    rw [←Real.rpow_mul_natCast hΛ.le]
    congr 1
    ring
  have hv : ((V q)^(χ/2))^2=(V q)^χ := by
    rw [←Real.rpow_mul_natCast (hV q)]
    congr 1
    ring
  unfold MeanBudgetEnergy.envelope prefactor
  simp only [mul_pow,div_pow,hp,hv]
  ring

end SHE.MeanDampedEnergy
