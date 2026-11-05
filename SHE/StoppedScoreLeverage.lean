module

public import SHE.RealGramFrame
public import SHE.HistoryLeverageMass
public import SHE.StoppedCanonicalScore
public import SHE.ProfileFrameRange

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
noncomputable section

namespace SHE.StoppedScoreLeverage
open Set MeasureTheory AddCircle Finset StoppedFourier StoppedGaussianFeatures GaussianAudit
  GaussianGramScore GaussianIncrement MeasurableGaussianScores GaussianProfileMark
open scoped InnerProductSpace
local instance stoppedScoreLeverage_periodPos : Fact (0 < 2*Real.pi) := ⟨by positivity⟩
variable {n : ℕ} (σ target : Fin n → ℝ) (center : Fin n → HeatCircle)

def referenceFeature (hages : ∀ i,σ i ≤ target i) (q : ℝ) :
    Fin n → Lp ℝ 2 (historyMeasure q) :=
  weightedFeature σ target center (fun _ => 1) measurable_const 1
    (fun _ => ⟨zero_le_one,le_rfl⟩) hages q

theorem referenceSynthesis_norm_sq (hages : ∀ i,σ i ≤ target i) (q : ℝ) (z : State n) :
    ‖featureSynthesis (referenceFeature σ target center hages q) z‖^2 =
      (fullPhysicalEnergy (historyF univ (fun i => (z i:ℂ)) σ target center) q).toReal := by
  rw [referenceFeature,weightedSynthesis_norm_sq]
  simp only [one_mul]
  exact realHistory_full_energy σ target center hages z q

theorem row_energy_integrable (hages : ∀ i,σ i ≤ target i) (q : ℝ) :
    Integrable (fun p => ‖stoppedRow σ target center p‖^2) (historyMeasure q) := by
  have hi (i : Fin n) : Integrable (fun p => stoppedRow σ target center p i ^2) (historyMeasure q) := by
    simpa only [realHistory_basisCoeff] using
      realHistory_square_product_integrable σ target center hages (basisCoeff i) q
  simpa only [EuclideanSpace.real_norm_sq_eq] using integrable_finsetSum univ (fun i _ => hi i)

theorem reference_covariance (hages : ∀ i,σ i ≤ target i) (q : ℝ) :
    Matrix.gram ℝ (referenceFeature σ target center hages q) =
      profileCovariance (historyMeasure q) (fun _ => 1) (stoppedRow σ target center) := by
  rw [referenceFeature,weightedFeature_gram]
  ext i j
  symm
  apply profileCovariance_entries
  exact profileCovariance_integrable (historyMeasure q) (fun _ => 1) (stoppedRow σ target center)
    aestronglyMeasurable_const (stoppedRow_measurable σ target center).aestronglyMeasurable
    (by simpa only [abs_one,one_mul] using row_energy_integrable σ target center hages q)

theorem row_mem_reference_range_ae (hages : ∀ i,σ i ≤ target i) (q : ℝ) :
    ∀ᵐ p ∂historyMeasure q,stoppedRow σ target center p ∈
      (Matrix.toEuclideanCLM (𝕜 := ℝ) (Matrix.gram ℝ (referenceFeature σ target center hages q))).range := by
  rw [reference_covariance]
  exact ae_frame_mem_gram_range (historyMeasure q) (stoppedRow σ target center)
    (stoppedRow_measurable σ target center).aestronglyMeasurable
    (row_energy_integrable σ target center hages q)

def referenceCoefficients (hages : ∀ i,σ i ≤ target i) (q : ℝ) :
    FrameIndex (referenceFeature σ target center hages q) → Fin n → ℂ :=
  fun k i => (frameCoefficients (referenceFeature σ target center hages q) k i : ℂ)

/-- A deterministic positive reference kernel, independent of every
variable coefficient profile, retaining the complete stopped history. -/
def referenceKernel (hages : ∀ i,σ i ≤ target i) (q : ℝ) : Domain → ℝ :=
  physicalLeverage (referenceCoefficients σ target center hages q) σ target center

theorem realHistory_eq_inner (z : State n) (p : Domain) :
    realHistory σ target center z p = inner ℝ z (stoppedRow σ target center p) := by
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp only [realHistory,dotProduct,star_trivial]
  exact sum_congr rfl (fun i _ => mul_comm _ _)

theorem referenceKernel_eq (hages : ∀ i,σ i ≤ target i) (q : ℝ) (p : Domain) :
    referenceKernel σ target center hages q p =
      ∑ k : FrameIndex (referenceFeature σ target center hages q),
        (inner ℝ (frameCoefficients (referenceFeature σ target center hages q) k)
          (stoppedRow σ target center p))^2 := by
  unfold referenceKernel physicalLeverage referenceCoefficients
  apply sum_congr rfl
  intro k hk
  rw [physicalHistory_eq_realHistory σ target center hages,Complex.norm_real,Real.norm_eq_abs,sq_abs,
    realHistory_eq_inner]

theorem referenceScore_eq_ae (hages : ∀ i,σ i ≤ target i) (q : ℝ) :
    (fun p => scoreVariance (Matrix.gram ℝ (referenceFeature σ target center hages q))
      (stoppedRow σ target center p)) =ᵐ[historyMeasure q]
      referenceKernel σ target center hages q := by
  filter_upwards [row_mem_reference_range_ae σ target center hages q] with p hp
  rw [scoreVariance_eq_frame _ hp,referenceKernel_eq]

/-- Canonical physical score energy is dominated by one deterministic
reference leverage kernel, uniformly over all bounded elliptic profiles. -/
theorem score_le_reference_ae (hages : ∀ i,σ i ≤ target i)
    (c : Domain → ℝ) (hc : Measurable c) (M : ℝ)
    (hcb : ∀ p,0 ≤ c p ∧ c p ≤ M) {ell : ℝ} (hell : 0 < ell)
    (hcl : ∀ p,ell ≤ c p) (q : ℝ) :
    ∀ᵐ p ∂historyMeasure q,
      scoreVariance (StoppedGaussianFeatures.stoppedCovariance σ target center c q)
        (stoppedRow σ target center p) ≤ referenceKernel σ target center hages q p / ell := by
  let v := referenceFeature σ target center hages q
  let w := weightedFeature σ target center c hc M hcb hages q
  have hdom (z : State n) : ell*‖featureSynthesis v z‖^2 ≤ ‖featureSynthesis w z‖^2 := by
    rw [referenceSynthesis_norm_sq]
    exact (weightedSynthesis_full_history_bounds σ target center c hc M hcb hages hcl q z).1
  filter_upwards [row_mem_reference_range_ae σ target center hages q,
    referenceScore_eq_ae σ target center hages q] with p hp he
  have hh := scoreVariance_le_of_gram_domination v w hell hdom hp
  rw [show Matrix.gram ℝ w=StoppedGaussianFeatures.stoppedCovariance σ target center c q from
    weightedFeature_gram σ target center c hc M hcb hages q,he] at hh
  exact hh

theorem reference_history_energy_le (hages : ∀ i,σ i ≤ target i) :
    (∑ k,‖historyTimeVector univ (referenceCoefficients σ target center hages 0 k)
      σ target center (fun i _ => hages i) 0‖^2) ≤ (n:ℝ) := by
  have he (k : FrameIndex (referenceFeature σ target center hages 0)) :
      ‖historyTimeVector univ (referenceCoefficients σ target center hages 0 k)
        σ target center (fun i _ => hages i) 0‖^2 = 1 := by
    rw [historyTimeVector_norm_sq]
    change (fullPhysicalEnergy (historyF univ
      (fun i => (frameCoefficients (referenceFeature σ target center hages 0) k i:ℂ))
        σ target center) 0).toReal = 1
    rw [← referenceSynthesis_norm_sq σ target center hages 0,
      (frameCoefficients_orthonormal (referenceFeature σ target center hages 0)).norm_eq_one k,one_pow]
  simp_rw [he]
  simpa only [sum_const,card_univ,nsmul_eq_mul,mul_one] using!
    (show (Fintype.card (FrameIndex (referenceFeature σ target center hages 0)):ℝ) ≤ (n:ℝ) from
      by exact_mod_cast frame_card_le (referenceFeature σ target center hages 0))

/-- Exact negative time-power mass for the deterministic reference
kernel, with only the observation count and no conditioning factor. -/
theorem referenceKernel_weighted_mass (hages : ∀ i,σ i ≤ target i) {s α : ℝ}
    (hs : 0 < s) (hα : -1 < α) (hα0 : α < 0) (hstop : ∀ i,s ≤ σ i) :
    Integrable (fun p => p.1^α*referenceKernel σ target center hages 0 p) (historyMeasure 0) ∧
      (∫ p,p.1^α*referenceKernel σ target center hages 0 p ∂historyMeasure 0) ≤
        (n:ℝ)*(s/2)^α*(1+2/(α+1)) := by
  let z := referenceCoefficients σ target center hages 0
  obtain ⟨hm,h0,hi,hmarginal⟩ := physicalLeverage_properties z σ target center hages
  obtain ⟨hw,hbound⟩ := rpow_historyLeverage_of_energy z σ target center hages hs hα hα0
    (Nat.cast_nonneg n) hstop (reference_history_energy_le σ target center hages)
  have hw0 : ∀ᵐ u ∂volume.restrict (Ici (0:ℝ)),0 ≤ u^α := by
    filter_upwards [ae_restrict_mem measurableSet_Ici] with u hu
    exact Real.rpow_nonneg hu α
  obtain ⟨hp,hpmass⟩ := weighted_kernel_mass (volume.restrict (Ici 0))
    (physicalLeverage z σ target center) hm h0 hi (fun u => u^α)
    (measurable_id.pow_const α) hw0 (historyLeverage z σ target center) hmarginal hw
  exact ⟨hp,hpmass.le.trans hbound⟩

/-- A coefficient-independent positive score kernel with the exact
weighted history mass used by the one-rough-leaf estimate. -/
theorem exists_score_kernel (hages : ∀ i,σ i ≤ target i) {s α ell : ℝ}
    (hs : 0 < s) (hα : -1 < α) (hα0 : α < 0) (hell : 0 < ell) (hstop : ∀ i,s ≤ σ i) :
    ∃ k : Domain → ℝ,Measurable k ∧ (∀ p,0 ≤ k p) ∧
      Integrable (fun p => p.1^α*k p) (historyMeasure 0) ∧
      (∫ p,p.1^α*k p ∂historyMeasure 0) ≤
        ((n:ℝ)/ell)*(s/2)^α*(1+2/(α+1)) ∧
      ∀ (c : Domain → ℝ) (hc : Measurable c) (M : ℝ)
        (hcb : ∀ p,0 ≤ c p ∧ c p ≤ M),
        (∀ p,ell ≤ c p) → ∀ᵐ p ∂historyMeasure 0,
        scoreVariance (StoppedGaussianFeatures.stoppedCovariance σ target center c 0)
          (stoppedRow σ target center p) ≤ k p := by
  let k : Domain → ℝ := fun p => referenceKernel σ target center hages 0 p/ell
  obtain ⟨hm,h0,hi,hmarginal⟩ := physicalLeverage_properties
    (referenceCoefficients σ target center hages 0) σ target center hages
  have hmass := referenceKernel_weighted_mass σ target center hages hs hα hα0 hstop
  have hki : Integrable (fun p => p.1^α*k p) (historyMeasure 0) := by
    simpa only [k,mul_div_assoc] using hmass.1.div_const ell
  refine ⟨k,hm.div_const ell,(fun p => div_nonneg (h0 p) hell.le),hki,?_,?_⟩
  · simp only [k,mul_div_assoc]
    simp_rw [div_eq_mul_inv,← mul_assoc]
    rw [integral_mul_const]
    convert! mul_le_mul_of_nonneg_right hmass.2 (inv_nonneg.mpr hell.le) using 1 <;> ring
  · intro c hc M hcb hcl
    exact score_le_reference_ae σ target center hages c hc M hcb hell hcl 0

/-- The deterministic reference score kernel acts on one actual L²
input with the sharp weighted history mass. All integrability follows
from the genuine translated physical kernel. -/
theorem referenceKernel_convolution_bound (hages : ∀ i,σ i ≤ target i) {s α ell : ℝ}
    (hs : 0 < s) (hα : -1 < α) (hα0 : α < 0) (hell : 0 < ell) (hstop : ∀ i,s ≤ σ i)
    (f : ℝ → CircleL2) (hf : AEStronglyMeasurable f (volume.restrict (Ici 0)))
    {K : ℝ} (hK : 0 ≤ K) (hfw : ∀ᵐ u ∂volume.restrict (Ici 0),‖f u‖ ≤ K*u^α) :
    Integrable (fun p : Domain => (referenceKernel σ target center hages 0 p/ell) •
      circleTranslate p.2 (f p.1)) (historyMeasure 0) ∧
      ‖∫ p : Domain,(referenceKernel σ target center hages 0 p/ell) •
        circleTranslate p.2 (f p.1) ∂historyMeasure 0‖ ≤
        K*(((n:ℝ)/ell)*(s/2)^α*(1+2/(α+1))) := by
  obtain ⟨hm,h0,hi,hmarginal⟩ := physicalLeverage_properties
    (referenceCoefficients σ target center hages 0) σ target center hages
  have hmass := referenceKernel_weighted_mass σ target center hages hs hα hα0 hstop
  let k : Domain → ℝ := fun p => referenceKernel σ target center hages 0 p/ell
  have hki : Integrable (fun p => p.1^α*k p) (historyMeasure 0) := by
    simpa only [k,mul_div_assoc] using hmass.1.div_const ell
  obtain ⟨hconv,hbound⟩ := circle_convolution_average_bound (volume.restrict (Ici 0)) k
    (hm.div_const ell) (fun p => div_nonneg (h0 p) hell.le) (fun u => u^α) f hf hK hfw hki
  refine ⟨hconv,hbound.trans (mul_le_mul_of_nonneg_left ?_ hK)⟩
  simp only [k,mul_div_assoc]
  simp_rw [div_eq_mul_inv,← mul_assoc]
  rw [integral_mul_const]
  convert! mul_le_mul_of_nonneg_right hmass.2 (inv_nonneg.mpr hell.le) using 1 <;> ring

end SHE.StoppedScoreLeverage
