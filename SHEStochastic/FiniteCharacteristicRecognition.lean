module

public import SHEStochastic.GaussianCharacteristicMartingale
public import SHEStochastic.ConditionalCharacteristic

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 900000
noncomputable section

namespace SHEStochastic.FiniteCharacteristicRecognition
open MeasureTheory ProbabilityTheory SHE Matrix
open scoped NNReal InnerProductSpace

variable {Ω ι : Type*} [MeasurableSpace Ω] [DecidableEq ι]
  (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ]
  (H : ℝ≥0) (W : ι → ℝ≥0 → Ω → ℝ)

def phase {n : ℕ} (a : Fin n → ι) (r : WordRecursion.State n) (t : ℝ≥0) (ω : Ω) : ℝ :=
  inner ℝ (WithLp.toLp 2 (fun i ↦ W (a i) t ω)) r

theorem phase_adapted (hW : ∀ i t, Measurable[F t] (W i t))
    {n : ℕ} (a : Fin n → ι) (r : WordRecursion.State n) (t : ℝ≥0) :
    Measurable[F t] (phase W a r t) := by
  have hw (i : Fin n) : Measurable[F t] (W (a i) t) := hW (a i) t
  letI : MeasurableSpace Ω := F t
  exact ((WithLp.measurable_toLp 2 (Fin n → ℝ)).comp
    (measurable_pi_iff.mpr hw)).inner measurable_const

/-- Finite characteristic martingales determine the Gaussian increment
law and independence from the ENTIRE given filtration. No abstract Levy
characterization or martingale representation is assumed. -/
theorem step (hW : ∀ i t, Measurable[F t] (W i t))
    (hChar : ∀ n (a : Fin n → ι) (r : WordRecursion.State n),
      Martingale (fun t ω ↦ Complex.exp
        (((phase W a r (min t H) ω-phase W a r 0 ω : ℝ) : ℂ)*Complex.I +
          (GaussianCharacteristicMartingale.variance a r * (min t H : ℝ≥0) : ℝ))) F μ)
    {n : ℕ} (a : Fin n → ι) (s t : ℝ≥0) (hst : s ≤ t) (htH : t ≤ H) :
    HasLaw (fun ω ↦ WithLp.toLp 2 (fun i ↦ W (a i) t ω-W (a i) s ω))
      (multivariateGaussian (0 : WordRecursion.State n)
        (BrownianFiniteCovariance.matrix a (fun _ ↦ t-s))) μ ∧
    Indep (MeasurableSpace.comap (fun ω ↦ WithLp.toLp 2 (fun i ↦ W (a i) t ω-W (a i) s ω))
      (borel (WordRecursion.State n))) (F s) μ := by
  let Z := fun ω ↦ WithLp.toLp 2 (fun i ↦ W (a i) t ω-W (a i) s ω)
  have hZ : Measurable Z := (WithLp.measurable_toLp 2 (Fin n → ℝ)).comp
    (measurable_pi_iff.mpr fun i ↦ ((hW (a i) t).mono (F.le t) le_rfl).sub
      ((hW (a i) s).mono (F.le s) le_rfl))
  apply ConditionalCharacteristic.law_and_independent (F s) (F.le s) hZ
  intro r A hA
  let c := GaussianCharacteristicMartingale.variance a r
  have hm := (hChar n a r).condExp_ae_eq hst
  simp only [min_eq_left htH, min_eq_left (hst.trans htH)] at hm
  have hX := (phase_adapted F W hW a r s).sub
    ((phase_adapted F W hW a r 0).mono (F.mono bot_le) le_rfl)
  have hY := ((phase_adapted F W hW a r t).mono (F.le t) le_rfl).sub
    ((phase_adapted F W hW a r 0).mono (F.le 0) le_rfl)
  have hh := GaussianCharacteristicMartingale.conditional_increment μ (F s) (F.le s)
    (fun ω ↦ phase W a r s ω-phase W a r 0 ω)
    (fun ω ↦ phase W a r t ω-phase W a r 0 ω) hX hY (c*s) (c*t) hm
  have he (ω : Ω) :
      (phase W a r t ω-phase W a r 0 ω)-(phase W a r s ω-phase W a r 0 ω) = inner ℝ (Z ω) r := by
    rw [sub_sub_sub_cancel_right, phase, phase, ← inner_sub_left]
    rfl
  simp_rw [he] at hh
  have hc : Complex.exp (-(c*t-c*s : ℝ)) =
      charFun (multivariateGaussian (0 : WordRecursion.State n)
        (BrownianFiniteCovariance.matrix a (fun _ ↦ t-s))) r := by
    rw [charFun_multivariateGaussian (BrownianFiniteCovariance.posSemidef a (fun _ ↦ t-s))]
    simp only [inner_zero_right, Complex.ofReal_zero, zero_mul, zero_sub]
    rw [GaussianCharacteristicMartingale.covariance_scale]
    congr 1
    dsimp only [c, GaussianCharacteristicMartingale.variance]
    rw [NNReal.coe_sub hst]
    push_cast
    ring
  rw [hc] at hh
  have hi : Integrable (fun ω ↦ Complex.exp ((inner ℝ (Z ω) r : ℂ)*Complex.I)) μ :=
    (integrable_const (1 : ℝ)).mono' (by fun_prop)
      (Filter.Eventually.of_forall fun ω ↦ by simp [Complex.norm_exp])
  calc
    _ = ∫ ω in A, μ[fun ω ↦ Complex.exp ((inner ℝ (Z ω) r : ℂ)*Complex.I) | F s] ω ∂μ :=
      (setIntegral_condExp (F.le s) hi hA).symm
    _ = _ := by
      rw [setIntegral_congr_ae (F.le s A hA) (hh.mono fun _ hx _ ↦ hx), integral_const]
      simp only [Measure.real, Measure.restrict_apply_univ]

end SHEStochastic.FiniteCharacteristicRecognition
