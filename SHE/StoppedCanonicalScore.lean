module

public import SHE.StoppedGaussianFields
public import SHE.StoppedGaussianScore

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section

/-! Canonical measurable Gaussian scores inherit the literal stopped-history
heat envelopes. The continuous heat-span evaluation is identified with the
physical heat row, rather than left as an abstract score direction. -/
namespace SHE.StoppedCanonicalScore
open Set MeasureTheory ProbabilityTheory Real AddCircle Finset StoppedFourier
  StoppedGaussianFeatures StoppedGaussianScore MeasurableGaussianScores
  GaussianGramScore GaussianIncrement HeatTorus HeatTorusKernel HeatChristoffel HeatProjection
  HeatHistoryScore RealHeatScore RealHeatEnergyScore
open scoped InnerProductSpace
local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

variable {n : ℕ}

theorem evaluation_ae (t : Fin n → ℝ) (a : Fin n → UnitAddCircle)
    (ht : ∀ i, 0 < t i) (f : heatSpan t a) :
    (fun x => evaluation t a ht x f) =ᵐ[haarAddCircle] (f : HeatTorus.CircleL2) := by
  have h := ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) haarAddCircle (continuousLift t a ht f)
  rw [toLp_continuousLift] at h
  exact h.symm

theorem unitHeatKernel_physical_ae {t : ℝ} (ht : 0 < t) (a : UnitAddCircle) :
    unitHeatKernel t a =ᵐ[haarAddCircle] fun x =>
      ProfileVariance.heatPhysical (4 * π ^ 2 * t) (CircleNormalization.scale 1 (2 * π) a)
        (CircleNormalization.scale 1 (2 * π) x) := by
  have h := (CircleNormalization.scale_measurePreserving 1 (2 * π)).quasiMeasurePreserving.ae
    (ProfileVariance.heatPhysical_ae (show 0 < 4 * π ^ 2 * t by positivity)
      (CircleNormalization.scale 1 (2 * π) a))
  filter_upwards [CircleNormalization.pull_ae 1 (2 * π)
    (circleHeat (4 * π ^ 2 * t) (CircleNormalization.scale 1 (2 * π) a)), h] with x hx hy
  exact hx.trans hy.symm

theorem realDamped_basis (σ target : Fin n → ℝ) (a : Fin n → UnitAddCircle)
    (u Λ : ℝ) (t : Fin n → ℝ)
    (hage : ∀ i, target i - u = 4 * π ^ 2 * t i) (hactive : ∀ i, u < σ i) (i : Fin n) :
    ((realDamped σ target a u Λ t hage hactive (EuclideanSpace.basisFun (Fin n) ℝ i) : heatSpan t a) :
      HeatTorus.CircleL2) = (exp (-Λ * (σ i - u)) : ℂ) • unitHeatKernel (t i) (a i) := by
  change pulledDampedCurrent σ target a u Λ (fun j =>
    ((EuclideanSpace.basisFun (Fin n) ℝ i) j : ℂ)) = _
  rw [pulledDampedCurrent_sum σ target a u Λ t hage hactive]
  rw [Finset.sum_eq_single i]
  · simp [EuclideanSpace.basisFun_apply]
  · intro j _ hji
    simp [EuclideanSpace.basisFun_apply, hji]
  · simp

theorem realCurrent_basis (σ target : Fin n → ℝ) (a : Fin n → UnitAddCircle)
    (u : ℝ) (t : Fin n → ℝ)
    (hage : ∀ i, target i - u = 4 * π ^ 2 * t i) (hactive : ∀ i, u < σ i) (i : Fin n) :
    ((realCurrent σ target a u t hage hactive (EuclideanSpace.basisFun (Fin n) ℝ i) : heatSpan t a) :
      HeatTorus.CircleL2) = unitHeatKernel (t i) (a i) := by
  change pulledCurrent σ target a u (fun j => ((EuclideanSpace.basisFun (Fin n) ℝ i) j : ℂ)) = _
  rw [pulledCurrent_sum σ target a u t hage hactive]
  simp [EuclideanSpace.basisFun_apply, PiLp.single_apply]

theorem evaluationDirection_damped_ae (σ target : Fin n → ℝ) (a : Fin n → UnitAddCircle)
    (u Λ : ℝ) (t : Fin n → ℝ) (ht : ∀ i, 0 < t i)
    (hage : ∀ i, target i - u = 4 * π ^ 2 * t i) (hactive : ∀ i, u < σ i) :
    (fun x => evaluationDirection t a ht (realDamped σ target a u Λ t hage hactive) x) =ᵐ[haarAddCircle]
      fun x => WithLp.toLp 2 (fun i => exp (-Λ * (σ i - u)) *
        (ProfileVariance.heatPhysical (target i - u) (nativeCenter a i)
          (CircleNormalization.scale 1 (2 * π) x)).re) := by
  have he (i : Fin n) := evaluation_ae t a ht
    (realDamped σ target a u Λ t hage hactive (EuclideanSpace.basisFun (Fin n) ℝ i))
  have hs (i : Fin n) := Lp.coeFn_smul (exp (-Λ * (σ i - u)) : ℂ) (unitHeatKernel (t i) (a i))
  have hk (i : Fin n) := unitHeatKernel_physical_ae (ht i) (a i)
  filter_upwards [ae_all_iff.mpr he, ae_all_iff.mpr hs, ae_all_iff.mpr hk] with x hx hs hk
  apply (WithLp.equiv 2 (Fin n → ℝ)).injective
  funext i
  change evaluationDirection t a ht (realDamped σ target a u Λ t hage hactive) x i = _
  rw [evaluationDirection_apply, realEvaluation_apply, hx i, realDamped_basis, hs i]
  rw [Pi.smul_apply, smul_eq_mul, hk i]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  change exp (-Λ * (σ i - u)) * (ProfileVariance.heatPhysical (4 * π ^ 2 * t i)
    (nativeCenter a i) (CircleNormalization.scale 1 (2 * π) x)).re =
    exp (-Λ * (σ i - u)) * (ProfileVariance.heatPhysical (target i - u)
      (nativeCenter a i) (CircleNormalization.scale 1 (2 * π) x)).re
  rw [hage i]

theorem evaluationDirection_sub (t : Fin n → ℝ) (a : Fin n → UnitAddCircle)
    (ht : ∀ i, 0 < t i) (S T : State n →ₗ[ℝ] heatSpan t a) (x : UnitAddCircle) :
    evaluationDirection t a ht (S - T) x =
      evaluationDirection t a ht S x - evaluationDirection t a ht T x := by
  apply ext_inner_left ℝ
  intro z
  rw [inner_sub_right, inner_evaluationDirection, inner_evaluationDirection,
    inner_evaluationDirection, LinearMap.sub_apply, map_sub]

theorem evaluationDirection_current_ae (σ target : Fin n → ℝ) (a : Fin n → UnitAddCircle)
    (u : ℝ) (t : Fin n → ℝ) (ht : ∀ i, 0 < t i)
    (hage : ∀ i, target i - u = 4 * π ^ 2 * t i) (hactive : ∀ i, u < σ i) :
    (fun x => evaluationDirection t a ht (realCurrent σ target a u t hage hactive) x) =ᵐ[haarAddCircle]
      fun x => WithLp.toLp 2 (fun i =>
        (ProfileVariance.heatPhysical (target i - u) (nativeCenter a i)
          (CircleNormalization.scale 1 (2 * π) x)).re) := by
  have he (i : Fin n) := evaluation_ae t a ht
    (realCurrent σ target a u t hage hactive (EuclideanSpace.basisFun (Fin n) ℝ i))
  have hk (i : Fin n) := unitHeatKernel_physical_ae (ht i) (a i)
  filter_upwards [ae_all_iff.mpr he, ae_all_iff.mpr hk] with x hx hk
  apply (WithLp.equiv 2 (Fin n → ℝ)).injective
  funext i
  change evaluationDirection t a ht (realCurrent σ target a u t hage hactive) x i = _
  rw [evaluationDirection_apply, realEvaluation_apply, hx i, realCurrent_basis, hk i]
  change (ProfileVariance.heatPhysical (4 * π ^ 2 * t i) (nativeCenter a i)
    (CircleNormalization.scale 1 (2 * π) x)).re =
    (ProfileVariance.heatPhysical (target i - u) (nativeCenter a i)
      (CircleNormalization.scale 1 (2 * π) x)).re
  rw [hage i]

def physicalDefectDirection (σ target : Fin n → ℝ) (a : Fin n → UnitAddCircle)
    (u Λ : ℝ) (x : UnitAddCircle) : State n :=
  WithLp.toLp 2 (fun i => (1 - exp (-Λ * (σ i - u))) *
    (ProfileVariance.heatPhysical (target i - u) (nativeCenter a i)
      (CircleNormalization.scale 1 (2 * π) x)).re)

theorem evaluationDirection_defect_ae (σ target : Fin n → ℝ) (a : Fin n → UnitAddCircle)
    (u Λ : ℝ) (t : Fin n → ℝ) (ht : ∀ i, 0 < t i)
    (hage : ∀ i, target i - u = 4 * π ^ 2 * t i) (hactive : ∀ i, u < σ i) :
    (fun x => evaluationDirection t a ht (realDefect σ target a u Λ t hage hactive) x) =ᵐ[haarAddCircle]
      physicalDefectDirection σ target a u Λ := by
  have hS : realDefect σ target a u Λ t hage hactive =
      realCurrent σ target a u t hage hactive - realDamped σ target a u Λ t hage hactive := rfl
  filter_upwards [evaluationDirection_current_ae σ target a u t ht hage hactive,
    evaluationDirection_damped_ae σ target a u Λ t ht hage hactive] with x hc hd
  rw [hS, evaluationDirection_sub, hc, hd]
  apply (WithLp.equiv 2 (Fin n → ℝ)).injective
  funext i
  change (ProfileVariance.heatPhysical (target i - u) (nativeCenter a i)
    (CircleNormalization.scale 1 (2 * π) x)).re -
    exp (-Λ * (σ i - u)) * (ProfileVariance.heatPhysical (target i - u) (nativeCenter a i)
      (CircleNormalization.scale 1 (2 * π) x)).re = (1 - exp (-Λ * (σ i - u))) *
    (ProfileVariance.heatPhysical (target i - u) (nativeCenter a i)
      (CircleNormalization.scale 1 (2 * π) x)).re
  ring

theorem scoreVariance_eq_physical (σ target : Fin n → ℝ) (center : Fin n → HeatCircle)
    (c : Domain → ℝ) (hc : Measurable c) (M : ℝ)
    (hcb : ∀ r, 0 ≤ c r ∧ c r ≤ M) (hages : ∀ i, σ i ≤ target i) (q : ℝ)
    {d : State n} {m : Lp ℝ 2 (historyMeasure q)}
    (hm : m ∈ (featureSynthesis (weightedFeature σ target center c hc M hcb hages q)).range)
    (hpair : ∀ z, inner ℝ (featureSynthesis (weightedFeature σ target center c hc M hcb hages q) z) m =
      inner ℝ z d) :
    scoreVariance (StoppedGaussianFeatures.stoppedCovariance σ target center c q) d = ‖m‖ ^ 2 := by
  rw [← weightedFeature_gram σ target center c hc M hcb hages q]
  exact physical_scoreVariance_eq _ hm hpair

theorem direction_mem_covariance_range (σ target : Fin n → ℝ) (center : Fin n → HeatCircle)
    (c : Domain → ℝ) (hc : Measurable c) (M : ℝ)
    (hcb : ∀ r, 0 ≤ c r ∧ c r ≤ M) (hages : ∀ i, σ i ≤ target i) (q : ℝ)
    {d : State n} {m : Lp ℝ 2 (historyMeasure q)}
    (hm : m ∈ (featureSynthesis (weightedFeature σ target center c hc M hcb hages q)).range)
    (hpair : ∀ z, inner ℝ (featureSynthesis (weightedFeature σ target center c hc M hcb hages q) z) m =
      inner ℝ z d) :
    d ∈ (Matrix.toEuclideanCLM (𝕜 := ℝ)
      (StoppedGaussianFeatures.stoppedCovariance σ target center c q)).range := by
  rw [← weightedFeature_gram σ target center c hc M hcb hages q]
  exact physical_direction_mem_range _ hm hpair

def physicalDampedDirection (σ target : Fin n → ℝ) (a : Fin n → UnitAddCircle)
    (u Λ : ℝ) (x : UnitAddCircle) : State n :=
  WithLp.toLp 2 (fun i => exp (-Λ * (σ i - u)) *
    (ProfileVariance.heatPhysical (target i - u) (nativeCenter a i)
      (CircleNormalization.scale 1 (2 * π) x)).re)

/-- The actual Borel damped Gaussian score, normalized by the entire
individually stopped covariance, obeys the proved original-target envelope.
No measurable physical representative is assumed. -/
theorem stopped_damped_score_bound (n : ℕ) :
    ∃ h K : ℝ, 0 < h ∧ h ≤ 1 ∧ 0 < K ∧
      ∀ (σ target : Fin n → ℝ) (a : Fin n → UnitAddCircle) (u Λ : ℝ), 0 < Λ →
      ∀ (t : Fin n → ℝ) (_ht : ∀ i, 0 < t i), (∀ i, t i ≤ h) →
      ∀ (_hage : ∀ i, target i - u = 4 * π ^ 2 * t i) (_hages : ∀ i, σ i ≤ target i)
      (δ : ℝ) (_hδ : 0 < δ) (_hstop : ∀ i, u + δ ≤ σ i)
      (c : Domain → ℝ) (_hc : Measurable c) (M ell : ℝ)
      (_hcb : ∀ r, 0 ≤ c r ∧ c r ≤ M), 0 < ell → (∀ r, ell ≤ c r) →
      ∀ᵐ x ∂haarAddCircle,
      physicalDampedDirection σ target a u Λ x ∈
        (Matrix.toEuclideanCLM (𝕜 := ℝ)
          (StoppedGaussianFeatures.stoppedCovariance σ target (nativeCenter a) c u)).range ∧
      scoreVariance (StoppedGaussianFeatures.stoppedCovariance σ target (nativeCenter a) c u)
        (physicalDampedDirection σ target a u Λ x) ≤
        (2 * K / (ell * δ)) * ∑ i, GlobalTorusHeatSpan.weight (t i) (a i) x := by
  obtain ⟨h, K, hh, hh1, hK, hrep⟩ := stopped_damped_representer n
  refine ⟨h, K, hh, hh1, hK, ?_⟩
  intro σ target a u Λ hΛ t ht hth hage hages δ hδ hstop c hc M ell hcb hell hcl
  have hactive (i : Fin n) : u < σ i := by linarith [hstop i]
  filter_upwards [evaluationDirection_damped_ae σ target a u Λ t ht hage hactive] with x hx
  obtain ⟨m, hm, hp, hb⟩ := hrep σ target a u Λ hΛ t ht hth hage hages δ hδ hstop c hc M ell hcb hell hcl x
  change evaluationDirection t a ht (realDamped σ target a u Λ t hage hactive) x =
    physicalDampedDirection σ target a u Λ x at hx
  rw [hx] at hp
  exact ⟨direction_mem_covariance_range σ target (nativeCenter a) c hc M hcb hages u hm hp,
    (scoreVariance_eq_physical σ target (nativeCenter a) c hc M hcb hages u hm hp).trans_le hb⟩

/-- The literal measurable defect score retains its squared clipped mass
against the true full stopped covariance, before any Gaussian moment or
spatial averaging is taken. -/
theorem stopped_defect_score_bound (n : ℕ) :
    ∃ h K : ℝ, 0 < h ∧ h ≤ 1 ∧ 0 < K ∧
      ∀ (σ target : Fin n → ℝ) (a : Fin n → UnitAddCircle) (u Λ : ℝ), 0 < Λ →
      ∀ (t : Fin n → ℝ) (_ht : ∀ i, 0 < t i), (∀ i, t i ≤ h) →
      ∀ (_hage : ∀ i, target i - u = 4 * π ^ 2 * t i) (_hages : ∀ i, σ i ≤ target i)
      (w A : ℝ) (_hw : 0 < w), 1 ≤ A →
      (∀ i, u + w ≤ σ i) → (∀ i, σ i ≤ u + A * w) →
      ∀ (c : Domain → ℝ) (_hc : Measurable c) (M ell : ℝ)
      (_hcb : ∀ r, 0 ≤ c r ∧ c r ≤ M), 0 < ell → (∀ r, ell ≤ c r) →
      ∀ᵐ x ∂haarAddCircle,
      physicalDefectDirection σ target a u Λ x ∈
        (Matrix.toEuclideanCLM (𝕜 := ℝ)
          (StoppedGaussianFeatures.stoppedCovariance σ target (nativeCenter a) c u)).range ∧
      scoreVariance (StoppedGaussianFeatures.stoppedCovariance σ target (nativeCenter a) c u)
        (physicalDefectDirection σ target a u Λ x) ≤
        (K * (max A 8 / w) * (min 1 (Λ * w)) ^ 2 / ell) *
          ∑ i, GlobalTorusHeatSpan.weight (t i) (a i) x := by
  obtain ⟨h, K, hh, hh1, hK, hrep⟩ := stopped_defect_representer n
  refine ⟨h, K, hh, hh1, hK, ?_⟩
  intro σ target a u Λ hΛ t ht hth hage hages w A hw hA hlower hupper c hc M ell hcb hell hcl
  have hactive (i : Fin n) : u < σ i := by linarith [hlower i]
  filter_upwards [evaluationDirection_defect_ae σ target a u Λ t ht hage hactive] with x hx
  obtain ⟨m, hm, hp, hb⟩ := hrep σ target a u Λ hΛ t ht hth hage hages w A hw hA
    hlower hupper c hc M ell hcb hell hcl x
  rw [hx] at hp
  exact ⟨direction_mem_covariance_range σ target (nativeCenter a) c hc M hcb hages u hm hp,
    (scoreVariance_eq_physical σ target (nativeCenter a) c hc M hcb hages u hm hp).trans_le hb⟩

end SHE.StoppedCanonicalScore
