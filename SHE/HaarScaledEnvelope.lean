module

public import SHE.HaarSeparatedTaylor
public import SHE.HeatKernelAgeComparison

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section

namespace SHE.FiniteHaar
open Finset Set MeasureTheory AddCircle CircleHeat HeatMarkov HeatKernelAgeComparison
local instance haarScaledEnvelope_periodPos : Fact (0 < (1:ℝ)) := ⟨zero_lt_one⟩

theorem clippedAge_cost {C w δ ρ : ℝ} (hδ : 0 < δ) (hw : 0 < w) (hw1 : w ≤ 1)
    (hδw : δ ≤ w) (hρhalf : ρ < 1/2) :
    (clippedAge C w)^(ρ-1/2)*(1+Real.log (clippedAge C w/δ)) ≤
      (1+Real.log (envelopeScale C))*w^(ρ-1/2)*(1+Real.log (w/δ)) := by
  have hv := clippedAge_bounds (C := C) hw hw1
  have hv0 := clippedAge_pos (C := C) hw
  have hR := envelopeScale_pos C
  have hlogR : 0 ≤ Real.log (envelopeScale C) := Real.log_nonneg (le_max_left _ _)
  have hlogw : 0 ≤ Real.log (w/δ) := Real.log_nonneg ((one_le_div hδ).mpr hδw)
  have hlogv : 0 ≤ Real.log (clippedAge C w/δ) := Real.log_nonneg ((one_le_div hδ).mpr (hδw.trans hv.1))
  have hp : (clippedAge C w)^(ρ-1/2) ≤ w^(ρ-1/2) :=
    Real.rpow_le_rpow_of_nonpos hw hv.1 (by linarith)
  have hl : Real.log (clippedAge C w/δ) ≤ Real.log (envelopeScale C)+Real.log (w/δ) := by
    have hh := Real.log_le_log hv0 hv.2.2
    rw [Real.log_mul hR.ne' hw.ne'] at hh
    rw [Real.log_div hv0.ne' hδ.ne',Real.log_div hw.ne' hδ.ne']
    linarith
  have hl' : 1+Real.log (clippedAge C w/δ) ≤ (1+Real.log (envelopeScale C))*(1+Real.log (w/δ)) := by
    nlinarith [mul_nonneg hlogR hlogw]
  have hh := mul_le_mul hp hl' (by linarith : 0 ≤ 1+Real.log (clippedAge C w/δ)) (Real.rpow_nonneg hw.le (ρ-1/2))
  exact hh.trans_eq (by ring)

/-- The manuscript's fixed enlarged Gaussian envelope p_(Cw), for
every C>0 and every 0<δ≤w≤1, including its positive-age tail. -/
theorem exists_global_scaled_envelope_trace (m U : ℝ) (hm : 0 < m) (j : ℕ)
    {ρ C : ℝ} (hρ : 0 < ρ) (hρhalf : ρ < 1/2) (hC : 0 < C) :
    ∃ J : ℝ,0 < J ∧ ∀ (Λ δ w K : ℝ) (hΛ : 1 ≤ Λ) (hδ : 0 < δ) (hw : 0 < w),
      w ≤ 1 → δ ≤ w → 0 ≤ K → ∀ (D : HeatDominatedKernel (C*w) K (by positivity)) (f : DyadicApproximation.RealL2),
      (∀ᵐ y ∂haarAddCircle,m ≤ (DyadicApproximation.realEmbed f y).re ∧
        (DyadicApproximation.realEmbed f y).re ≤ U) →
      ∀ (v : Fin (j+1) → DyadicApproximation.RealL2) (M : Fin (j+1) → ℝ),
      (∀ i,0 ≤ M i) →
      (∀ i,i ≠ 0 → ∀ᵐ y ∂haarAddCircle,‖DyadicApproximation.realEmbed (v i) y‖ ≤ M i) →
      Summable (fun q : HaarNode => ‖separatedHeat Λ ρ δ hΛ hρ.le D.operator
        (iteratedFDeriv ℝ (j+1) (globalHaarColumn q) (DyadicApproximation.realEmbed f)
          (fun i => DyadicApproximation.realEmbed (v i)))‖^2) ∧
      (∑' q : HaarNode,‖separatedHeat Λ ρ δ hΛ hρ.le D.operator
        (iteratedFDeriv ℝ (j+1) (globalHaarColumn q) (DyadicApproximation.realEmbed f)
          (fun i => DyadicApproximation.realEmbed (v i)))‖^2) ≤
        J*K^2*w^(ρ-1/2)*δ^(-ρ)*(1+Real.log (w/δ))*
          StepInput.negativeEnergy 1 Λ ρ (DyadicApproximation.realEmbed (v 0))*
          (∏ i ∈ univ.erase (0 : Fin (j+1)),M i)^2 := by
  obtain ⟨J,hJ,htrace⟩ := exists_global_separated_negative_trace m U hm j hρ hρhalf
  obtain ⟨L,hL,henvelope⟩ := exists_clipped_envelope hC
  have hR : 0 < 1+Real.log (envelopeScale C) := by
    have hh := Real.log_nonneg (le_max_left 1 C)
    dsimp only [envelopeScale]
    linarith
  refine ⟨J*L^2*(1+Real.log (envelopeScale C)),by positivity,?_⟩
  intro Λ δ w K hΛ hδ hw hw1 hδw hK D f hf v M hM hv
  let a := clippedAge C w
  have ha := clippedAge_pos (C := C) hw
  have hab := clippedAge_bounds (C := C) hw hw1
  let D' : HeatDominatedKernel a (K*L) ha := {
    operator := D.operator
    kernel := D.kernel
    measurable_kernel := D.measurable_kernel
    kernel_bound := fun x y => (D.kernel_bound x y).trans ((mul_le_mul_of_nonneg_left
      (henvelope w hw hw1 (y-x)) hK).trans_eq (by ring))
    representation := D.representation }
  have hn := htrace Λ δ a (K*L) hΛ hδ ha hab.2.1 (hδw.trans hab.1) (mul_nonneg hK hL.le) D' f hf v M hM hv
  have hE : 0 ≤ StepInput.negativeEnergy 1 Λ ρ (DyadicApproximation.realEmbed (v 0)) := by
    rw [← NegativeNash.energy_eq_negativeEnergy Λ ρ (zero_lt_one.trans_le hΛ)]
    unfold NegativeNash.energy
    positivity
  have hc := clippedAge_cost (C := C) hδ hw hw1 hδw hρhalf
  have hh := mul_le_mul_of_nonneg_left hc (by positivity : 0 ≤ J*(K*L)^2*δ^(-ρ)*
    StepInput.negativeEnergy 1 Λ ρ (DyadicApproximation.realEmbed (v 0))*
    (∏ i ∈ univ.erase (0 : Fin (j+1)),M i)^2)
  exact ⟨hn.1,hn.2.trans (by dsimp only [a,D']; nlinarith only [hh])⟩

end SHE.FiniteHaar
