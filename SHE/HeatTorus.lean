module

public import SHE.GlobalHeatSpan
public import SHE.HeatPeriodicEnergy
public import SHE.HeatPeriodicEnvelope
public import SHE.FourierParseval
public import SHE.CircleNormalization
public import SHE.CircleCut

/-! Collision-uniform small-time localization of genuine periodized finite
heat spans. The line theorem, periodization tails, and normalization are
actual proved analytic inputs. -/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace SHE.HeatTorus
open MeasureTheory Set Real SHE.HeatLine SHE.HeatPeriodization SHE.HeatPeriodicBounds
  SHE.HeatPeriodicEnergy SHE.HeatPeriodicEnvelope
open scoped FourierTransform

abbrev CircleL2 := Lp ℂ 2 (AddCircle.haarAddCircle (T := 1))

def periodizationL2 {q : ℕ} (t a : Fin q → ℝ) (ht : ∀ i, 0 < t i) (f : ℂ → ℂ)
    (hf : f ∈ Submodule.span ℂ (Set.range (fun i => heatEntire (t i) (a i)))) : CircleL2 :=
  ContinuousMap.toLp 2 AddCircle.haarAddCircle ℂ (circlePeriodize t a ht f hf)

theorem periodizationL2_ae {q : ℕ} (t a : Fin q → ℝ) (ht : ∀ i, 0 < t i) (f : ℂ → ℂ)
    (hf : f ∈ Submodule.span ℂ (Set.range (fun i => heatEntire (t i) (a i)))) :
    periodizationL2 t a ht f hf =ᵐ[AddCircle.haarAddCircle] circlePeriodize t a ht f hf :=
  ContinuousMap.coeFn_toLp _ _

theorem periodizationL2_fourierCoeff {q : ℕ} (t a : Fin q → ℝ) (ht : ∀ i, 0 < t i)
    (f : ℂ → ℂ) (hf : f ∈ Submodule.span ℂ (Set.range (fun i => heatEntire (t i) (a i))))
    (n : ℤ) : fourierCoeff (periodizationL2 t a ht f hf) n = 𝓕 (fun y : ℝ => f (y : ℂ)) n := by
  rw [← fourierCoeff_circlePeriodize t a ht f hf]
  unfold fourierCoeff
  apply integral_congr_ae
  filter_upwards [periodizationL2_ae t a ht f hf] with x hx
  rw [hx]

theorem periodizationL2_norm_sq {q : ℕ} (t a : Fin q → ℝ) (ht : ∀ i, 0 < t i)
    (f : ℂ → ℂ) (hf : f ∈ Submodule.span ℂ (Set.range (fun i => heatEntire (t i) (a i)))) :
    ‖periodizationL2 t a ht f hf‖ ^ 2 =
      ∫ x : UnitAddCircle, ‖circlePeriodize t a ht f hf x‖ ^ 2 ∂AddCircle.haarAddCircle := by
  rw [SHE.StoppedFourier.L2_norm_sq_eq_integral]
  apply integral_congr_ae
  filter_upwards [periodizationL2_ae t a ht f hf] with x hx
  rw [hx]

theorem periodizationL2_interval_energy {q : ℕ} (t a : Fin q → ℝ) (ht : ∀ i, 0 < t i)
    (f : ℂ → ℂ) (hf : f ∈ Submodule.span ℂ (Set.range (fun i => heatEntire (t i) (a i)))) :
    (∫ x : ℝ in Icc (-1 / 2 : ℝ) (1 / 2),
      ‖periodize (fun y : ℝ => f (y : ℂ)) x‖ ^ 2) = ‖periodizationL2 t a ht f hf‖ ^ 2 := by
  rw [periodizationL2_norm_sq]
  have hvol : (volume : Measure UnitAddCircle) = AddCircle.haarAddCircle := by
    rw [AddCircle.volume_eq_smul_haarAddCircle]
    norm_num
  rw [← hvol]
  have h := UnitAddCircle.integral_preimage (-1 / 2 : ℝ)
    (fun x : UnitAddCircle => ‖circlePeriodize t a ht f hf x‖ ^ 2)
  rw [integral_Icc_eq_integral_Ioc]
  convert! h using 1
  · congr 1
    norm_num

/-- A uniform small-time cutoff makes genuine periodization bounded below
on the complete finite line heat span, including all coefficient cancellations. -/
theorem exists_heat_span_periodization_energy_bound (q : ℕ) {η : ℝ}
    (hη : 0 < η) (hη1 : η ≤ 1) :
    ∃ h₀ : ℝ, 0 < h₀ ∧ h₀ ≤ 1 ∧ ∀ (t a : Fin q → ℝ) (ht : ∀ i, 0 < t i),
      (∀ i, t i ≤ h₀) → (∀ i, |a i| ≤ 1 / 2 - η) →
      ∀ (f : ℂ → ℂ) (hf : f ∈ Submodule.span ℂ (Set.range (fun i => heatEntire (t i) (a i)))),
      (∫ x : ℝ, ‖f (x : ℂ)‖ ^ 2) ≤ 4 * ‖periodizationL2 t a ht f hf‖ ^ 2 := by
  obtain ⟨C, hC, hline⟩ := SHE.GlobalHeatSpan.global_heat_span_envelope q
  obtain ⟨h₀, hh₀, hh₀1, hsmall⟩ := exists_periodization_energy_cutoff q C η
  refine ⟨h₀, hh₀, hh₀1, ?_⟩
  intro t a ht hth ha f hf
  obtain ⟨hi, hb⟩ := hline t a ht f hf
  have hP : IntegrableOn (fun x : ℝ => ‖periodize (fun y : ℝ => f (y : ℂ)) x‖ ^ 2)
      (Icc (-1 / 2 : ℝ) (1 / 2)) :=
    ((continuous_periodize_heat_span t a ht f hf).norm.pow 2).continuousOn.integrableOn_compact isCompact_Icc
  rw [← periodizationL2_interval_energy]
  apply finite_heat_periodization_energy_comparison t a (fun y : ℝ => f (y : ℂ)) hC.le
    ht hth hh₀1 hη hη1 ha hi hP (hsmall h₀ hh₀ le_rfl)
  simpa only [SHE.GlobalHeatSpan.weight] using hb

/-- The actual continuous periodized finite heat span has a uniform local
Gaussian envelope in its own circle L² norm. The real lifts lie inside one
common cut; CircleCut supplies such a cut for every finite family. -/
theorem exists_periodized_heat_span_envelope (q : ℕ) {η : ℝ}
    (hη : 0 < η) (hη1 : η ≤ 1) :
    ∃ h₀ C : ℝ, 0 < h₀ ∧ h₀ ≤ 1 ∧ 0 < C ∧
      ∀ (t a : Fin q → ℝ) (ht : ∀ i, 0 < t i), (∀ i, t i ≤ h₀) →
      (∀ i, |a i| ≤ 1 / 2 - η) →
      ∀ (f : ℂ → ℂ) (hf : f ∈ Submodule.span ℂ (Set.range (fun i => heatEntire (t i) (a i)))),
      ∀ x : UnitAddCircle, ‖circlePeriodize t a ht f hf x‖ ^ 2 ≤
        C * ‖periodizationL2 t a ht f hf‖ ^ 2 * ∑ i, (sqrt (t i))⁻¹ *
          exp (-(dist x (a i : UnitAddCircle)) ^ 2 / (8 * t i)) := by
  obtain ⟨D, hD, hline⟩ := SHE.GlobalHeatSpan.global_heat_span_envelope q
  obtain ⟨h₀, hh₀, hh₀1, henergy⟩ := exists_heat_span_periodization_energy_bound q hη hη1
  let C : ℝ := 1 + 4 * D * periodicEnvelopeConstant ^ 2 * (q : ℝ)
  have hC : 0 < C := by dsimp only [C]; positivity
  refine ⟨h₀, C, hh₀, hh₀1, hC, ?_⟩
  intro t a ht hth ha f hf x
  induction x using Quotient.inductionOn with
  | _ x =>
    rw [circlePeriodize_coe]
    obtain ⟨_, hb⟩ := hline t a ht f hf
    have hE : 0 ≤ ∫ y : ℝ, ‖f (y : ℂ)‖ ^ 2 := integral_nonneg (fun _ => sq_nonneg _)
    have hb' := finite_heat_periodization_pointwise_envelope t a (fun y : ℝ => f (y : ℂ))
      (mul_nonneg hD.le hE) ht (fun i => (hth i).trans hh₀1)
      (by simpa only [SHE.GlobalHeatSpan.weight] using hb) x
    have he := henergy t a ht hth ha f hf
    let W : ℝ := ∑ i, (sqrt (t i))⁻¹ *
      exp (-(dist (x : UnitAddCircle) (a i : UnitAddCircle)) ^ 2 / (8 * t i))
    have hW : 0 ≤ W := Finset.sum_nonneg (fun _ _ => by positivity)
    have hfactor : 0 ≤ D * periodicEnvelopeConstant ^ 2 * (q : ℝ) * W := by positivity
    have hm := mul_le_mul_of_nonneg_left he hfactor
    have hb'' : ‖periodize (fun y : ℝ => f (y : ℂ)) x‖ ^ 2 ≤
        (D * periodicEnvelopeConstant ^ 2 * (q : ℝ) * W) *
          (∫ y : ℝ, ‖f (y : ℂ)‖ ^ 2) := by
      convert! hb' using 1
      ring
    apply hb''.trans (hm.trans ?_)
    change (D * periodicEnvelopeConstant ^ 2 * (q : ℝ) * W) *
      (4 * ‖periodizationL2 t a ht f hf‖ ^ 2) ≤ C * ‖periodizationL2 t a ht f hf‖ ^ 2 * W
    dsimp only [C]
    nlinarith [mul_nonneg (sq_nonneg ‖periodizationL2 t a ht f hf‖) hW]

end SHE.HeatTorus
