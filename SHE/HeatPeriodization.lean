module

public import SHE.HeatCluster
public import Mathlib.Analysis.SpecialFunctions.Gaussian.PoissonSummation
public import Mathlib.Analysis.PSeries

/-! Genuine integer periodization of finite line heat spans. -/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace SHE.HeatPeriodization
open MeasureTheory Set Filter Asymptotics TopologicalSpace SHE.HeatLine SHE.HeatCluster
open scoped FourierTransform

def periodize (f : ℝ → ℂ) (x : ℝ) : ℂ := ∑' n : ℤ, f (x + n)

theorem heat_span_rapid_decay {q : ℕ} (t a : Fin q → ℝ) (ht : ∀ i, 0 < t i)
    (f : ℂ → ℂ)
    (hf : f ∈ Submodule.span ℂ (Set.range (fun i => heatEntire (t i) (a i)))) (b : ℝ) :
    (fun x : ℝ => f (x : ℂ)) =O[cocompact ℝ] (fun x : ℝ => |x| ^ b) := by
  have hfg := heat_span_gaussian t a f hf
  obtain ⟨d, hd⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hfg
  have hb (i : Fin q) :
      (fun x : ℝ => SHE.HeatAnnihilator.gaussian (heatParameter (t i) (a i)) (x : ℂ))
        =O[cocompact ℝ] (fun x : ℝ => |x| ^ b) := by
    apply (cexp_neg_quadratic_isLittleO_abs_rpow_cocompact
      (a := -((1 / (4 * t i) : ℝ) : ℂ)) ?_
      ((a i / (2 * t i) : ℝ) : ℂ) b).isBigO
    simp only [Complex.neg_re, Complex.ofReal_re]
    have hti := ht i
    exact neg_neg_of_pos (by positivity)
  have hsum := Asymptotics.IsBigO.sum (s := Finset.univ)
    (fun i _ => (hb i).const_mul_left (d i))
  convert! hsum using 1
  funext x
  have hx := congrFun hd (x : ℂ)
  simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using hx.symm

theorem heat_span_locally_summable_translates {q : ℕ} (t a : Fin q → ℝ)
    (ht : ∀ i, 0 < t i) (f : ℂ → ℂ)
    (hf : f ∈ Submodule.span ℂ (Set.range (fun i => heatEntire (t i) (a i))))
    (K : Compacts ℝ) :
    Summable (fun n : ℤ =>
      ‖((⟨fun x : ℝ => f (x : ℂ), continuous_heat_span t a f hf⟩ : C(ℝ, ℂ)).comp
        (ContinuousMap.addRight n)).restrict K‖) := by
  apply summable_of_isBigO (Real.summable_abs_int_rpow (by norm_num : (1 : ℝ) < 2))
  exact (isBigO_norm_restrict_cocompact
    (⟨fun x : ℝ => f (x : ℂ), continuous_heat_span t a f hf⟩ : C(ℝ, ℂ))
    (by norm_num : (0 : ℝ) < 2) (heat_span_rapid_decay t a ht f hf (-2)) K).comp_tendsto
      Int.tendsto_coe_cofinite

def continuousPeriodize {q : ℕ} (t a : Fin q → ℝ) (f : ℂ → ℂ)
    (hf : f ∈ Submodule.span ℂ (Set.range (fun i => heatEntire (t i) (a i)))) : C(ℝ, ℂ) :=
  ∑' n : ℤ, (⟨fun x : ℝ => f (x : ℂ), continuous_heat_span t a f hf⟩ : C(ℝ, ℂ)).comp
    (ContinuousMap.addRight n)

theorem continuousPeriodize_apply {q : ℕ} (t a : Fin q → ℝ) (ht : ∀ i, 0 < t i)
    (f : ℂ → ℂ) (hf : f ∈ Submodule.span ℂ (Set.range (fun i => heatEntire (t i) (a i))))
    (x : ℝ) : continuousPeriodize t a f hf x = periodize (fun y : ℝ => f (y : ℂ)) x := by
  have hs := ContinuousMap.summable_of_locally_summable_norm
    (heat_span_locally_summable_translates t a ht f hf)
  convert! (ContinuousMap.tsum_apply hs x).symm using 1

theorem continuous_periodize_heat_span {q : ℕ} (t a : Fin q → ℝ) (ht : ∀ i, 0 < t i)
    (f : ℂ → ℂ) (hf : f ∈ Submodule.span ℂ (Set.range (fun i => heatEntire (t i) (a i)))) :
    Continuous (periodize (fun y : ℝ => f (y : ℂ))) := by
  have he := funext (continuousPeriodize_apply t a ht f hf)
  rw [← he]
  exact (continuousPeriodize t a f hf).continuous

theorem periodic_periodize_heat_span {q : ℕ} (t a : Fin q → ℝ) (ht : ∀ i, 0 < t i)
    (f : ℂ → ℂ) (hf : f ∈ Submodule.span ℂ (Set.range (fun i => heatEntire (t i) (a i)))) :
    Function.Periodic (periodize (fun y : ℝ => f (y : ℂ))) 1 := by
  have h := (⟨fun x : ℝ => f (x : ℂ), continuous_heat_span t a f hf⟩ : C(ℝ, ℂ)).periodic_tsum_comp_add_zsmul 1
  have hp : Function.Periodic (continuousPeriodize t a f hf) 1 := by
    simpa only [continuousPeriodize, zsmul_eq_mul, mul_one] using h
  intro x
  rw [← continuousPeriodize_apply t a ht f hf, ← continuousPeriodize_apply t a ht f hf]
  exact hp x

def circlePeriodize {q : ℕ} (t a : Fin q → ℝ) (ht : ∀ i, 0 < t i)
    (f : ℂ → ℂ) (hf : f ∈ Submodule.span ℂ (Set.range (fun i => heatEntire (t i) (a i)))) :
    C(UnitAddCircle, ℂ) :=
  ⟨(periodic_periodize_heat_span t a ht f hf).lift,
    continuous_coinduced_dom.mpr (continuous_periodize_heat_span t a ht f hf)⟩

theorem circlePeriodize_coe {q : ℕ} (t a : Fin q → ℝ) (ht : ∀ i, 0 < t i)
    (f : ℂ → ℂ) (hf : f ∈ Submodule.span ℂ (Set.range (fun i => heatEntire (t i) (a i))))
    (x : ℝ) : circlePeriodize t a ht f hf (x : UnitAddCircle) =
      periodize (fun y : ℝ => f (y : ℂ)) x := by
  exact Function.Periodic.lift_coe (periodic_periodize_heat_span t a ht f hf) x

/-- Genuine Poisson coefficient identity for the actual continuous circle
periodization of every finite heat span. -/
theorem fourierCoeff_circlePeriodize {q : ℕ} (t a : Fin q → ℝ) (ht : ∀ i, 0 < t i)
    (f : ℂ → ℂ) (hf : f ∈ Submodule.span ℂ (Set.range (fun i => heatEntire (t i) (a i))))
    (n : ℤ) : fourierCoeff (circlePeriodize t a ht f hf) n =
      𝓕 (fun y : ℝ => f (y : ℂ)) n := by
  have h := Real.fourierCoeff_tsum_comp_add
    (heat_span_locally_summable_translates t a ht f hf) n
  convert! h using 2
  funext x
  induction x using Quotient.inductionOn with
  | _ x =>
    rw [circlePeriodize_coe, Function.Periodic.lift_coe]
    simp only [zsmul_eq_mul, mul_one]
    change periodize (fun y : ℝ => f (y : ℂ)) x = continuousPeriodize t a f hf x
    exact (continuousPeriodize_apply t a ht f hf x).symm

end SHE.HeatPeriodization
