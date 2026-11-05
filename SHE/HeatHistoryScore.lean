module

public import SHE.HeatChristoffel

/-! The literal stopped-history current rows, normalized to the unit circle,
and their covariance-normalized spatial score envelopes. -/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace SHE.HeatHistoryScore
open MeasureTheory Set Real AddCircle SHE.HeatTorus SHE.HeatTorusKernel
  SHE.HeatProjection SHE.HeatChristoffel SHE.StoppedFourier
open scoped InnerProductSpace
local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

variable {n : ℕ} (σ target : Fin n → ℝ) (a : Fin n → UnitAddCircle) (u : ℝ)

def pulledCurrent : (Fin n → ℂ) →ₗ[ℂ] SHE.HeatTorus.CircleL2 :=
  (SHE.CircleNormalization.pull 1 (2 * π)).toLinearMap.comp
    (currentLinearMap Finset.univ σ target (fun i => SHE.CircleNormalization.scale 1 (2 * π) (a i)) u)

def pulledDampedCurrent (Λ : ℝ) : (Fin n → ℂ) →ₗ[ℂ] SHE.HeatTorus.CircleL2 :=
  (SHE.CircleNormalization.pull 1 (2 * π)).toLinearMap.comp
    (dampedCurrentLinearMap Finset.univ σ target
      (fun i => SHE.CircleNormalization.scale 1 (2 * π) (a i)) Λ u)

theorem pulledCurrent_sum (t : Fin n → ℝ)
    (hage : ∀ i, target i - u = 4 * π ^ 2 * t i) (hactive : ∀ i, u < σ i)
    (z : Fin n → ℂ) :
    pulledCurrent σ target a u z = ∑ i, z i • unitHeatKernel (t i) (a i) := by
  change SHE.CircleNormalization.pull 1 (2 * π)
    (historyF Finset.univ z σ target (fun i => SHE.CircleNormalization.scale 1 (2 * π) (a i)) u) = _
  simp only [historyF, hactive, ite_true, map_sum, map_smul, hage,
    unitHeatKernel]

theorem pulledDampedCurrent_sum (Λ : ℝ) (t : Fin n → ℝ)
    (hage : ∀ i, target i - u = 4 * π ^ 2 * t i) (hactive : ∀ i, u < σ i)
    (z : Fin n → ℂ) :
    pulledDampedCurrent σ target a u Λ z =
      ∑ i, ((exp (-Λ * (σ i - u)) : ℂ) * z i) • unitHeatKernel (t i) (a i) := by
  change SHE.CircleNormalization.pull 1 (2 * π)
    (historyG Finset.univ z σ target (fun i => SHE.CircleNormalization.scale 1 (2 * π) (a i)) Λ u) = _
  simp only [historyG, hactive, ite_true, map_sum, map_smul, hage,
    unitHeatKernel, smul_smul]

def currentHeatRow (t : Fin n → ℝ)
    (hage : ∀ i, target i - u = 4 * π ^ 2 * t i) (hactive : ∀ i, u < σ i) :
    (Fin n → ℂ) →ₗ[ℂ] heatSpan t a :=
  (pulledCurrent σ target a u).codRestrict (heatSpan t a) (by
    intro z
    rw [pulledCurrent_sum σ target a u t hage hactive z]
    apply Submodule.sum_mem
    intro i _
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩))

def dampedHeatRow (Λ : ℝ) (t : Fin n → ℝ)
    (hage : ∀ i, target i - u = 4 * π ^ 2 * t i) (hactive : ∀ i, u < σ i) :
    (Fin n → ℂ) →ₗ[ℂ] heatSpan t a :=
  (pulledDampedCurrent σ target a u Λ).codRestrict (heatSpan t a) (by
    intro z
    rw [pulledDampedCurrent_sum σ target a u Λ t hage hactive z]
    apply Submodule.sum_mem
    intro i _
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩))

theorem currentHeatRow_norm_sq (t : Fin n → ℝ)
    (hage : ∀ i, target i - u = 4 * π ^ 2 * t i) (hactive : ∀ i, u < σ i)
    (z : Fin n → ℂ) :
    ‖currentHeatRow σ target a u t hage hactive z‖ ^ 2 =
      ‖historyF Finset.univ z σ target
        (fun i => SHE.CircleNormalization.scale 1 (2 * π) (a i)) u‖ ^ 2 := by
  change ‖SHE.CircleNormalization.pull 1 (2 * π) _‖ ^ 2 = _
  rw [(SHE.CircleNormalization.pull 1 (2 * π)).norm_map]
  rfl

theorem dampedHeatRow_norm_sq (Λ : ℝ) (t : Fin n → ℝ)
    (hage : ∀ i, target i - u = 4 * π ^ 2 * t i) (hactive : ∀ i, u < σ i)
    (z : Fin n → ℂ) :
    ‖dampedHeatRow σ target a u Λ t hage hactive z‖ ^ 2 =
      ‖historyG Finset.univ z σ target
        (fun i => SHE.CircleNormalization.scale 1 (2 * π) (a i)) Λ u‖ ^ 2 := by
  change ‖SHE.CircleNormalization.pull 1 (2 * π) _‖ ^ 2 = _
  rw [(SHE.CircleNormalization.pull 1 (2 * π)).norm_map]
  rfl

theorem currentHeatRow_covariance_dom {G : Type*}
    [NormedAddCommGroup G] [InnerProductSpace ℂ G]
    (t : Fin n → ℝ) (hage : ∀ i, target i - u = 4 * π ^ 2 * t i)
    (hages : ∀ i, σ i ≤ target i) {δ c : ℝ} (hδ : 0 < δ) (hc : 0 < c)
    (hstop : ∀ i, u + δ ≤ σ i) (C : (Fin n → ℂ) →ₗ[ℂ] G)
    (hcov : ∀ z, c * (fullPhysicalEnergy (historyF Finset.univ z σ target
      (fun i => SHE.CircleNormalization.scale 1 (2 * π) (a i))) u).toReal ≤ ‖C z‖ ^ 2) :
    ∀ z, (c * δ / 2) *
      ‖currentHeatRow σ target a u t hage (fun i => by linarith [hstop i]) z‖ ^ 2 ≤ ‖C z‖ ^ 2 := by
  intro z
  rw [currentHeatRow_norm_sq]
  have hb := stopped_current_row_bound Finset.univ z σ target
    (fun i => SHE.CircleNormalization.scale 1 (2 * π) (a i)) (fun i _ => hages i)
    hδ (fun i _ => hstop i)
  calc
    _ ≤ (c * δ / 2) * ((2 / δ) * (fullPhysicalEnergy (historyF Finset.univ z σ target
        (fun i => SHE.CircleNormalization.scale 1 (2 * π) (a i))) u).toReal) :=
      mul_le_mul_of_nonneg_left hb (by positivity)
    _ = c * (fullPhysicalEnergy (historyF Finset.univ z σ target
        (fun i => SHE.CircleNormalization.scale 1 (2 * π) (a i))) u).toReal := by
      field_simp
    _ ≤ _ := hcov z

theorem dampedHeatRow_covariance_dom {G : Type*}
    [NormedAddCommGroup G] [InnerProductSpace ℂ G]
    (Λ : ℝ) (hΛ : 0 < Λ) (t : Fin n → ℝ)
    (hage : ∀ i, target i - u = 4 * π ^ 2 * t i)
    (hages : ∀ i, σ i ≤ target i) {δ c : ℝ} (hδ : 0 < δ) (hc : 0 < c)
    (hstop : ∀ i, u + δ ≤ σ i) (C : (Fin n → ℂ) →ₗ[ℂ] G)
    (hcov : ∀ z, c * (fullPhysicalEnergy (historyF Finset.univ z σ target
      (fun i => SHE.CircleNormalization.scale 1 (2 * π) (a i))) u).toReal ≤ ‖C z‖ ^ 2) :
    ∀ z, (c * δ / 2) *
      ‖dampedHeatRow σ target a u Λ t hage (fun i => by linarith [hstop i]) z‖ ^ 2 ≤ ‖C z‖ ^ 2 := by
  intro z
  rw [dampedHeatRow_norm_sq]
  have hb := stopped_damped_current_row_bound Finset.univ z σ target
    (fun i => SHE.CircleNormalization.scale 1 (2 * π) (a i)) (fun i _ => hages i)
    hΛ hδ (fun i _ => hstop i)
  calc
    _ ≤ (c * δ / 2) * ((2 / δ) * (fullPhysicalEnergy (historyF Finset.univ z σ target
        (fun i => SHE.CircleNormalization.scale 1 (2 * π) (a i))) u).toReal) :=
      mul_le_mul_of_nonneg_left hb (by positivity)
    _ = c * (fullPhysicalEnergy (historyF Finset.univ z σ target
        (fun i => SHE.CircleNormalization.scale 1 (2 * π) (a i))) u).toReal := by
      field_simp
    _ ≤ _ := hcov z

/-- The actual damped row, normalized by any covariance dominating the
original full stopped history, has a positive physical Gaussian envelope.
The damping remains on the original stopping ages, while the envelope
uses the original target ages. -/
theorem finite_damped_history_score_bound (n : ℕ) :
    ∃ h K : ℝ, 0 < h ∧ h ≤ 1 ∧ 0 < K ∧
      ∀ (σ target : Fin n → ℝ) (a : Fin n → UnitAddCircle) (u Λ : ℝ), 0 < Λ →
      ∀ (t : Fin n → ℝ) (ht : ∀ i, 0 < t i), (∀ i, t i ≤ h) →
      ∀ (hage : ∀ i, target i - u = 4 * π ^ 2 * t i) (_hages : ∀ i, σ i ≤ target i),
      ∀ (δ c : ℝ) (hδ : 0 < δ) (_hc : 0 < c) (hstop : ∀ i, u + δ ≤ σ i),
      ∀ {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
      (C : (Fin n → ℂ) →ₗ[ℂ] G),
      (∀ z, c * (fullPhysicalEnergy (historyF Finset.univ z σ target
        (fun i => SHE.CircleNormalization.scale 1 (2 * π) (a i))) u).toReal ≤ ‖C z‖ ^ 2) →
      ∀ x : UnitAddCircle, ∃ m ∈ C.range,
      (∀ z, inner ℂ (C z) m = star (evaluation t a ht x
        (dampedHeatRow σ target a u Λ t hage (fun i => by linarith [hstop i]) z))) ∧
      ‖m‖ ^ 2 ≤ (2 * K / (c * δ)) * ∑ i, SHE.GlobalTorusHeatSpan.weight (t i) (a i) x := by
  obtain ⟨h, K, hh, hh1, hK, hscore⟩ := finite_heat_covariance_score_bound n
  refine ⟨h, K, hh, hh1, hK, ?_⟩
  intro σ target a u Λ hΛ t ht hth hage hages δ c hδ hc hstop G _ _ _ C hcov x
  have hdom := dampedHeatRow_covariance_dom σ target a u Λ hΛ t hage hages hδ hc hstop C hcov
  obtain ⟨m, hm, hpair, hn⟩ := hscore t a ht hth
    (dampedHeatRow σ target a u Λ t hage (fun i => by linarith [hstop i])) C
    (c * δ / 2) (by positivity) hdom x
  refine ⟨m, hm, hpair, ?_⟩
  convert! hn using 1
  congr 1
  field_simp

def defectHeatRow (Λ : ℝ) (t : Fin n → ℝ)
    (hage : ∀ i, target i - u = 4 * π ^ 2 * t i) (hactive : ∀ i, u < σ i) :
    (Fin n → ℂ) →ₗ[ℂ] heatSpan t a :=
  currentHeatRow σ target a u t hage hactive - dampedHeatRow σ target a u Λ t hage hactive

theorem defectHeatRow_norm_sq (Λ : ℝ) (t : Fin n → ℝ)
    (hage : ∀ i, target i - u = 4 * π ^ 2 * t i) (hactive : ∀ i, u < σ i)
    (z : Fin n → ℂ) :
    ‖defectHeatRow σ target a u Λ t hage hactive z‖ ^ 2 =
      ‖historyF Finset.univ z σ target (fun i => SHE.CircleNormalization.scale 1 (2 * π) (a i)) u -
        historyG Finset.univ z σ target (fun i => SHE.CircleNormalization.scale 1 (2 * π) (a i)) Λ u‖ ^ 2 := by
  change ‖SHE.CircleNormalization.pull 1 (2 * π) _ -
    SHE.CircleNormalization.pull 1 (2 * π) _‖ ^ 2 = _
  rw [← map_sub, (SHE.CircleNormalization.pull 1 (2 * π)).norm_map]
  rfl

/-- The clipped mass defect is retained in the actual covariance score.
The covariance is the original full stopped-history covariance, and the
physical heat envelope retains the original target ages. -/
theorem finite_defect_history_score_bound (n : ℕ) :
    ∃ h K : ℝ, 0 < h ∧ h ≤ 1 ∧ 0 < K ∧
      ∀ (σ target : Fin n → ℝ) (a : Fin n → UnitAddCircle) (u Λ : ℝ), 0 < Λ →
      ∀ (t : Fin n → ℝ) (ht : ∀ i, 0 < t i), (∀ i, t i ≤ h) →
      ∀ (hage : ∀ i, target i - u = 4 * π ^ 2 * t i) (_hages : ∀ i, σ i ≤ target i),
      ∀ (w M c : ℝ) (hw : 0 < w), 1 ≤ M → 0 < c →
      ∀ (hlower : ∀ i, u + w ≤ σ i), (∀ i, σ i ≤ u + M * w) →
      ∀ {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
      (C : (Fin n → ℂ) →ₗ[ℂ] G),
      (∀ z, c * (fullPhysicalEnergy (historyF Finset.univ z σ target
        (fun i => SHE.CircleNormalization.scale 1 (2 * π) (a i))) u).toReal ≤ ‖C z‖ ^ 2) →
      ∀ x : UnitAddCircle, ∃ m ∈ C.range,
      (∀ z, inner ℂ (C z) m = star (evaluation t a ht x
        (defectHeatRow σ target a u Λ t hage (fun i => by linarith [hlower i]) z))) ∧
      ‖m‖ ^ 2 ≤ (K * (max M 8 / w) * (min 1 (Λ * w)) ^ 2 / c) *
        ∑ i, SHE.GlobalTorusHeatSpan.weight (t i) (a i) x := by
  obtain ⟨h, K, hh, hh1, hK, hscore⟩ := finite_heat_energy_score_bound n
  refine ⟨h, K, hh, hh1, hK, ?_⟩
  intro σ target a u Λ hΛ t ht hth hage hages w M c hw hM hc hlower hupper G _ _ _ C hcov x
  let S := defectHeatRow σ target a u Λ t hage (fun i => by linarith [hlower i])
  let E := fun z => (fullPhysicalEnergy (historyF Finset.univ z σ target
    (fun i => SHE.CircleNormalization.scale 1 (2 * π) (a i))) u).toReal
  let L := sqrt (max M 8 / w) * min 1 (Λ * w)
  have hmax : 0 ≤ max M 8 / w := by positivity
  have hL : 0 ≤ L := mul_nonneg (sqrt_nonneg _) (le_min (by norm_num) (by positivity))
  have hLsq : L ^ 2 = (max M 8 / w) * (min 1 (Λ * w)) ^ 2 := by
    dsimp only [L]
    rw [mul_pow, sq_sqrt hmax]
  have hrow (z : Fin n → ℂ) : ‖S z‖ ^ 2 ≤ L ^ 2 * E z := by
    rw [hLsq]
    change ‖defectHeatRow σ target a u Λ t hage _ z‖ ^ 2 ≤ _
    rw [defectHeatRow_norm_sq]
    have hb := stopped_current_difference_clipped Finset.univ z σ target
      (fun i => SHE.CircleNormalization.scale 1 (2 * π) (a i)) (fun i _ => hages i)
      hΛ hw hM (fun i _ => hlower i) (fun i _ => hupper i)
    convert! hb using 1; dsimp only [E]; ring
  obtain ⟨m, hm, hp, hn⟩ := hscore t a ht hth S C E c L hc hL hrow hcov x
  refine ⟨m, hm, hp, ?_⟩
  rw [hLsq] at hn
  convert! hn using 1
  ring

end SHE.HeatHistoryScore
