/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho

Conditional-expectation algebra adapted from BracketCompensator.lean,
formal-mathfin 3c41aee9bf2d9743f9e66b439f90d1635843d2d2. The scalar
natural-filtration integral is replaced by abstract random variables;
the application uses the already proved Hilbert-noise conditional isometry.
-/
module

public import SHEStochastic.PredictableBracket

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section

namespace SHEStochastic.SquareCompensator
open MeasureTheory
open scoped NNReal ENNReal
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- The square-compensator calculation needs only conditional first and
second moments; all stochastic construction is outside this algebra lemma. -/
theorem conditional {m : MeasurableSpace Ω} (hm : m ≤ mΩ)
    (Ma Mb Aa Ab : Ω → ℝ) (hMa : MemLp Ma 2 μ) (hMb : MemLp Mb 2 μ)
    (hAai : Integrable Aa μ) (hAbi : Integrable Ab μ)
    (hMaAe : AEStronglyMeasurable[m] Ma μ) (hAaAe : AEStronglyMeasurable[m] Aa μ)
    (hmean : μ[Mb | m] =ᵐ[μ] Ma)
    (hvar : μ[(fun ω ↦ (Mb ω - Ma ω) ^ 2) | m] =ᵐ[μ] μ[(Ab - Aa) | m]) :
    μ[(fun ω ↦ Mb ω ^ 2 - Ab ω) | m] =ᵐ[μ] (fun ω ↦ Ma ω ^ 2 - Aa ω) := by
  have hMa2 : Integrable (fun ω ↦ Ma ω ^ 2) μ := hMa.integrable_sq
  have hMb2 : Integrable (fun ω ↦ Mb ω ^ 2) μ := hMb.integrable_sq
  have hMbi : Integrable Mb μ := hMb.integrable one_le_two
  have hcross : Integrable (fun ω ↦ Mb ω * Ma ω) μ :=
    (MemLp.mul (hf := hMa) (hφ := hMb)).integrable le_rfl
  have hCi : Integrable (fun ω ↦ Mb ω * Ma ω - Ma ω ^ 2) μ := hcross.sub hMa2
  have hdiff : Integrable (fun ω ↦ (Mb ω - Ma ω) ^ 2) μ := by
    rw [show (fun ω ↦ (Mb ω - Ma ω) ^ 2)
        = fun ω ↦ Mb ω ^ 2 - (Mb ω * Ma ω + Mb ω * Ma ω) + Ma ω ^ 2 from
      funext fun ω ↦ by ring]
    exact (hMb2.sub (hcross.add hcross)).add hMa2
  have e1 : μ[(fun ω ↦ Mb ω * Ma ω) | m] =ᵐ[μ] (fun ω ↦ Ma ω * Ma ω) := by
    refine (condExp_mul_of_aestronglyMeasurable_right hMaAe hcross hMbi).trans ?_
    filter_upwards [hmean] with ω hω
    change (μ[Mb | m]) ω * Ma ω = Ma ω * Ma ω
    rw [hω]
  have e2 : μ[(fun ω ↦ Ma ω ^ 2) | m] =ᵐ[μ] (fun ω ↦ Ma ω ^ 2) :=
    condExp_of_aestronglyMeasurable' hm (hMaAe.pow 2) hMa2
  have e3 : μ[Aa | m] =ᵐ[μ] Aa := condExp_of_aestronglyMeasurable' hm hAaAe hAai
  have eC : μ[(fun ω ↦ Mb ω * Ma ω - Ma ω ^ 2) | m] =ᵐ[μ] (fun _ ↦ (0 : ℝ)) := by
    refine (condExp_sub hcross hMa2 _).trans ?_
    filter_upwards [e1, e2] with ω h1 h2
    change (μ[(fun ω ↦ Mb ω * Ma ω) | m]) ω - (μ[(fun ω ↦ Ma ω ^ 2) | m]) ω = 0
    rw [h1, h2, sq]
    ring
  have eB : μ[(Ab - Aa) | m] =ᵐ[μ] (fun ω ↦ (μ[Ab | m]) ω - Aa ω) := by
    refine (condExp_sub hAbi hAai _).trans ?_
    filter_upwards [e3] with ω h
    change (μ[Ab | m]) ω - (μ[Aa | m]) ω = _
    rw [h]
  have eS : μ[(fun ω ↦ Mb ω ^ 2) | m] =ᵐ[μ]
      (fun ω ↦ (μ[(fun ω ↦ (Mb ω - Ma ω) ^ 2) | m]) ω + Ma ω ^ 2) := by
    rw [show (fun ω ↦ Mb ω ^ 2)
        = ((fun ω ↦ (Mb ω - Ma ω) ^ 2) + (fun ω ↦ Mb ω * Ma ω - Ma ω ^ 2))
            + ((fun ω ↦ Mb ω * Ma ω - Ma ω ^ 2) + (fun ω ↦ Ma ω ^ 2)) from
      funext fun ω ↦ by simp only [Pi.add_apply]; ring]
    refine (condExp_add (hdiff.add hCi) (hCi.add hMa2) _).trans ?_
    filter_upwards [condExp_add hdiff hCi m, condExp_add hCi hMa2 m, eC, e2] with ω h1 h2 h3 h4
    simp only [Pi.add_apply] at h1 h2 ⊢
    rw [h1, h2, h3, h4]
    ring
  refine (condExp_sub hMb2 hAbi _).trans ?_
  filter_upwards [eS, hvar, eB] with ω h1 h2 h3
  change (μ[(fun ω ↦ Mb ω ^ 2) | m]) ω - (μ[Ab | m]) ω = Ma ω ^ 2 - Aa ω
  rw [h1, h2, h3]
  ring

end SHEStochastic.SquareCompensator

namespace SHEStochastic.PredictableBracket
open MeasureTheory SHE SHE.PredictableL2 SHE.StoppedItoInputs
open scoped NNReal ENNReal
variable {Ω C : Type*} [MeasurableSpace Ω] [NormedAddCommGroup C] [InnerProductSpace ℝ C]
  [MeasurableSpace C] [BorelSpace C] [SecondCountableTopology C]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {μ : Measure Ω} [IsProbabilityMeasure μ] {H : ℝ≥0}

/-- The actual pathwise energy compensates the square of the same
stochastic integral, in the full original filtration. -/
theorem condExp_square_sub_energy (J : StandardTerminalIto (C := C) (E := ℝ) F μ H)
    (hlocal : StandardTerminalPastLocality J) (u : Process (E := C) F μ H)
    {a b : ℝ≥0} (hab : a ≤ b) :
    μ[(fun ω ↦ J.integral (stop F μ H b u) ω ^ 2 - energy u b ω) | F a] =ᵐ[μ]
      (fun ω ↦ J.integral (stop F μ H a u) ω ^ 2 - energy u a ω) := by
  obtain ⟨Z, hZ, hrep⟩ := stopped_integral_adapted F μ H J a u
  apply SquareCompensator.conditional (F.le a) _ _ _ _
    (Lp.memLp _) (Lp.memLp _) (integrable u a) (integrable u b)
    (hZ.aestronglyMeasurable.congr hrep.symm)
    (measurable u a).stronglyMeasurable.aestronglyMeasurable
    (ConditionalBracket.condExp_stopped J hlocal hab u)
  exact (ConditionalBracket.condExp_increment_second J hlocal hab u).trans
    (condExp_congr_ae (band_eq_sub u hab))

/-- Adapted versions of the integral yield an honest square-compensator
martingale; the energy is the original time integral of the squared norm. -/
theorem square_compensator_martingale (J : StandardTerminalIto (C := C) (E := ℝ) F μ H)
    (hlocal : StandardTerminalPastLocality J) (u : Process (E := C) F μ H)
    {M : ℝ≥0 → Ω → ℝ} (hm : StronglyAdapted F M)
    (hrep : ∀ t, M t =ᵐ[μ] (J.integral (stop F μ H t u) : Ω → ℝ)) :
    Martingale (fun t ω ↦ M t ω ^ 2 - energy u t ω) F μ := by
  refine ⟨fun t ↦ (hm t).pow 2 |>.sub (measurable u t).stronglyMeasurable, fun a b hab ↦ ?_⟩
  have he (t : ℝ≥0) : (fun ω ↦ M t ω ^ 2 - energy u t ω) =ᵐ[μ]
      (fun ω ↦ J.integral (stop F μ H t u) ω ^ 2 - energy u t ω) := by
    filter_upwards [hrep t] with ω h
    rw [h]
  exact (condExp_congr_ae (he b)).trans
    ((condExp_square_sub_energy J hlocal u hab).trans (he a).symm)

end SHEStochastic.PredictableBracket
