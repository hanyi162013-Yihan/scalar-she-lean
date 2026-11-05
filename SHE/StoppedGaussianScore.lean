module

public import SHE.StoppedGaussianFeatures
public import SHE.RealHeatEnergyScore
public import SHE.HeatHistoryScore

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

/-! Actual real Gaussian scores normalized against the entire weighted
individually stopped history, with original target ages and clipped mass. -/
namespace SHE.StoppedGaussianScore
open Set MeasureTheory Real AddCircle Finset StoppedFourier HeatTorus HeatTorusKernel HeatProjection
  HeatChristoffel HeatHistoryScore RealHeatScore RealHeatEnergyScore StoppedGaussianFeatures
  GaussianGramScore GaussianIncrement
open scoped InnerProductSpace Matrix.Norms.L2Operator

local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

variable {n : ℕ}

def complexCoefficients : State n →ₗ[ℝ] (Fin n → ℂ) where
  toFun z i := (z i : ℂ)
  map_add' z w := by funext i; simp only [PiLp.add_apply, Pi.add_apply, Complex.ofReal_add]
  map_smul' b z := by
    funext i
    simp only [PiLp.smul_apply, Pi.smul_apply, smul_eq_mul, Complex.ofReal_mul,
      RingHom.id_apply, Complex.real_smul]

variable (σ target : Fin n → ℝ) (a : Fin n → UnitAddCircle) (u : ℝ)

abbrev nativeCenter : Fin n → HeatCircle := fun i => CircleNormalization.scale 1 (2 * π) (a i)

def realCurrent (t : Fin n → ℝ) (hage : ∀ i, target i - u = 4 * π ^ 2 * t i)
    (hactive : ∀ i, u < σ i) : State n →ₗ[ℝ] heatSpan t a :=
  ((currentHeatRow σ target a u t hage hactive).restrictScalars ℝ).comp complexCoefficients

def realDamped (Λ : ℝ) (t : Fin n → ℝ) (hage : ∀ i, target i - u = 4 * π ^ 2 * t i)
    (hactive : ∀ i, u < σ i) : State n →ₗ[ℝ] heatSpan t a :=
  ((dampedHeatRow σ target a u Λ t hage hactive).restrictScalars ℝ).comp complexCoefficients

def realDefect (Λ : ℝ) (t : Fin n → ℝ) (hage : ∀ i, target i - u = 4 * π ^ 2 * t i)
    (hactive : ∀ i, u < σ i) : State n →ₗ[ℝ] heatSpan t a :=
  ((defectHeatRow σ target a u Λ t hage hactive).restrictScalars ℝ).comp complexCoefficients

theorem realDamped_norm_sq (Λ : ℝ) (t : Fin n → ℝ)
    (hage : ∀ i, target i - u = 4 * π ^ 2 * t i) (hactive : ∀ i, u < σ i) (z : State n) :
    ‖realDamped σ target a u Λ t hage hactive z‖ ^ 2 =
      ‖historyG univ (fun i => (z i : ℂ)) σ target (nativeCenter a) Λ u‖ ^ 2 :=
  dampedHeatRow_norm_sq σ target a u Λ t hage hactive (fun i => (z i : ℂ))

theorem realDefect_norm_sq (Λ : ℝ) (t : Fin n → ℝ)
    (hage : ∀ i, target i - u = 4 * π ^ 2 * t i) (hactive : ∀ i, u < σ i) (z : State n) :
    ‖realDefect σ target a u Λ t hage hactive z‖ ^ 2 =
      ‖historyF univ (fun i => (z i : ℂ)) σ target (nativeCenter a) u -
        historyG univ (fun i => (z i : ℂ)) σ target (nativeCenter a) Λ u‖ ^ 2 :=
  defectHeatRow_norm_sq σ target a u Λ t hage hactive (fun i => (z i : ℂ))

/-- Any proved physical row-energy bound yields the actual real Gaussian
Riesz score. The covariance domination is discharged from the true weighted
stopped-feature integral and pointwise ellipticity. -/
theorem stopped_energy_representer (n : ℕ) :
    ∃ h K : ℝ, 0 < h ∧ h ≤ 1 ∧ 0 < K ∧
      ∀ (σ target : Fin n → ℝ) (a : Fin n → UnitAddCircle) (u : ℝ)
      (t : Fin n → ℝ) (ht : ∀ i, 0 < t i), (∀ i, t i ≤ h) →
      ∀ (hages : ∀ i, σ i ≤ target i) (c : StoppedGaussianFeatures.Domain → ℝ)
      (hc : Measurable c) (M ell : ℝ) (hcb : ∀ p, 0 ≤ c p ∧ c p ≤ M),
      0 < ell → (∀ p, ell ≤ c p) →
      ∀ (S : State n →ₗ[ℝ] heatSpan t a) (L : ℝ), 0 ≤ L →
      (∀ z, ‖S z‖ ^ 2 ≤ L ^ 2 *
        (fullPhysicalEnergy (historyF univ (fun i => (z i : ℂ)) σ target (nativeCenter a)) u).toReal) →
      ∀ x : UnitAddCircle,
      ∃ m ∈ (featureSynthesis (weightedFeature σ target (nativeCenter a) c hc M hcb hages u)).range,
      (∀ z, inner ℝ (featureSynthesis (weightedFeature σ target (nativeCenter a) c hc M hcb hages u) z) m =
        inner ℝ z (evaluationDirection t a ht S x)) ∧
      ‖m‖ ^ 2 ≤ (K * L ^ 2 / ell) * ∑ i, GlobalTorusHeatSpan.weight (t i) (a i) x := by
  obtain ⟨h, K, hh, hh1, hK, hscore⟩ := finite_real_heat_energy_score_bound n
  refine ⟨h, K, hh, hh1, hK, ?_⟩
  intro σ target a u t ht hth hages c hc M ell hcb hell hcl S L hL hrow x
  let v := weightedFeature σ target (nativeCenter a) c hc M hcb hages u
  let E := fun z : State n =>
    (fullPhysicalEnergy (historyF univ (fun i => (z i : ℂ)) σ target (nativeCenter a)) u).toReal
  have hcov (z : State n) : ell * E z ≤ ‖featureSynthesis v z‖ ^ 2 :=
    (weightedSynthesis_full_history_bounds σ target (nativeCenter a) c hc M hcb hages hcl u z).1
  obtain ⟨m, hm, hp, hn⟩ := hscore t a ht hth S (featureSynthesis v) E ell L hell hL hrow hcov x
  refine ⟨m, hm, ?_, hn⟩
  intro z
  exact (hp z).trans (inner_evaluationDirection t a ht S x z).symm

/-- Actual damped covariance scores use the full original stopped history,
while the spatial envelope retains the original target ages. -/
theorem stopped_damped_representer (n : ℕ) :
    ∃ h K : ℝ, 0 < h ∧ h ≤ 1 ∧ 0 < K ∧
      ∀ (σ target : Fin n → ℝ) (a : Fin n → UnitAddCircle) (u Λ : ℝ), 0 < Λ →
      ∀ (t : Fin n → ℝ) (ht : ∀ i, 0 < t i), (∀ i, t i ≤ h) →
      ∀ (hage : ∀ i, target i - u = 4 * π ^ 2 * t i) (hages : ∀ i, σ i ≤ target i)
      (δ : ℝ) (hδ : 0 < δ) (hstop : ∀ i, u + δ ≤ σ i)
      (c : StoppedGaussianFeatures.Domain → ℝ) (hc : Measurable c) (M ell : ℝ)
      (hcb : ∀ p, 0 ≤ c p ∧ c p ≤ M), 0 < ell → (∀ p, ell ≤ c p) →
      ∀ x : UnitAddCircle,
      ∃ m ∈ (featureSynthesis (weightedFeature σ target (nativeCenter a) c hc M hcb hages u)).range,
      (∀ z, inner ℝ (featureSynthesis (weightedFeature σ target (nativeCenter a) c hc M hcb hages u) z) m =
        inner ℝ z (evaluationDirection t a ht
          (realDamped σ target a u Λ t hage (fun i => by linarith [hstop i])) x)) ∧
      ‖m‖ ^ 2 ≤ (2 * K / (ell * δ)) * ∑ i, GlobalTorusHeatSpan.weight (t i) (a i) x := by
  obtain ⟨h, K, hh, hh1, hK, hscore⟩ := stopped_energy_representer n
  refine ⟨h, K, hh, hh1, hK, ?_⟩
  intro σ target a u Λ hΛ t ht hth hage hages δ hδ hstop c hc M ell hcb hell hcl x
  let S := realDamped σ target a u Λ t hage (fun i => by linarith [hstop i])
  have hrow (z : State n) : ‖S z‖ ^ 2 ≤ (sqrt (2 / δ)) ^ 2 *
      (fullPhysicalEnergy (historyF univ (fun i => (z i : ℂ)) σ target (nativeCenter a)) u).toReal := by
    rw [sq_sqrt (by positivity : 0 ≤ 2 / δ)]
    change ‖realDamped σ target a u Λ t hage _ z‖ ^ 2 ≤ _
    rw [realDamped_norm_sq]
    exact stopped_damped_current_row_bound univ (fun i => (z i : ℂ)) σ target (nativeCenter a)
      (fun i _ => hages i) hΛ hδ (fun i _ => hstop i)
  obtain ⟨m, hm, hp, hn⟩ := hscore σ target a u t ht hth hages c hc M ell hcb hell hcl S
    (sqrt (2 / δ)) (sqrt_nonneg _) hrow x
  refine ⟨m, hm, hp, ?_⟩
  rw [sq_sqrt (by positivity : 0 ≤ 2 / δ)] at hn
  convert! hn using 1
  congr 1
  field_simp

/-- The actual full-history Gaussian defect score retains its squared clipped
mass factor, including the zero-clip case, without replacing target ages. -/
theorem stopped_defect_representer (n : ℕ) :
    ∃ h K : ℝ, 0 < h ∧ h ≤ 1 ∧ 0 < K ∧
      ∀ (σ target : Fin n → ℝ) (a : Fin n → UnitAddCircle) (u Λ : ℝ), 0 < Λ →
      ∀ (t : Fin n → ℝ) (ht : ∀ i, 0 < t i), (∀ i, t i ≤ h) →
      ∀ (hage : ∀ i, target i - u = 4 * π ^ 2 * t i) (hages : ∀ i, σ i ≤ target i)
      (w A : ℝ) (hw : 0 < w), 1 ≤ A →
      ∀ (hlower : ∀ i, u + w ≤ σ i), (∀ i, σ i ≤ u + A * w) →
      ∀ (c : StoppedGaussianFeatures.Domain → ℝ) (hc : Measurable c) (M ell : ℝ)
      (hcb : ∀ p, 0 ≤ c p ∧ c p ≤ M), 0 < ell → (∀ p, ell ≤ c p) →
      ∀ x : UnitAddCircle,
      ∃ m ∈ (featureSynthesis (weightedFeature σ target (nativeCenter a) c hc M hcb hages u)).range,
      (∀ z, inner ℝ (featureSynthesis (weightedFeature σ target (nativeCenter a) c hc M hcb hages u) z) m =
        inner ℝ z (evaluationDirection t a ht
          (realDefect σ target a u Λ t hage (fun i => by linarith [hlower i])) x)) ∧
      ‖m‖ ^ 2 ≤ (K * (max A 8 / w) * (min 1 (Λ * w)) ^ 2 / ell) *
        ∑ i, GlobalTorusHeatSpan.weight (t i) (a i) x := by
  obtain ⟨h, K, hh, hh1, hK, hscore⟩ := stopped_energy_representer n
  refine ⟨h, K, hh, hh1, hK, ?_⟩
  intro σ target a u Λ hΛ t ht hth hage hages w A hw hA hlower hupper c hc M ell hcb hell hcl x
  let S := realDefect σ target a u Λ t hage (fun i => by linarith [hlower i])
  let L := sqrt (max A 8 / w) * min 1 (Λ * w)
  have hmax : 0 ≤ max A 8 / w := by positivity
  have hL : 0 ≤ L := mul_nonneg (sqrt_nonneg _) (le_min (by norm_num) (by positivity))
  have hLsq : L ^ 2 = (max A 8 / w) * (min 1 (Λ * w)) ^ 2 := by
    dsimp only [L]
    rw [mul_pow, sq_sqrt hmax]
  have hrow (z : State n) : ‖S z‖ ^ 2 ≤ L ^ 2 *
      (fullPhysicalEnergy (historyF univ (fun i => (z i : ℂ)) σ target (nativeCenter a)) u).toReal := by
    rw [hLsq]
    change ‖realDefect σ target a u Λ t hage _ z‖ ^ 2 ≤ _
    rw [realDefect_norm_sq]
    have hb := stopped_current_difference_clipped univ (fun i => (z i : ℂ)) σ target (nativeCenter a)
      (fun i _ => hages i) hΛ hw hA (fun i _ => hlower i) (fun i _ => hupper i)
    convert! hb using 1
    ring
  obtain ⟨m, hm, hp, hn⟩ := hscore σ target a u t ht hth hages c hc M ell hcb hell hcl S L hL hrow x
  refine ⟨m, hm, hp, ?_⟩
  rw [hLsq] at hn
  convert! hn using 1
  ring

end SHE.StoppedGaussianScore
