module

public import SHE.HaarScaledEnvelope

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1800000
noncomputable section

namespace SHE.FiniteHaar
open Finset Set MeasureTheory AddCircle CircleHeat
local instance haarScaledTaylor_periodPos : Fact (0 < (1:ℝ)) := ⟨zero_lt_one⟩

theorem exists_global_scaled_taylor_trace (m U : ℝ) (hm : 0 < m) (j : ℕ)
    {ρ C : ℝ} (hρ : 0 < ρ) (hρhalf : ρ < 1/2) (hC : 0 < C) :
    ∃ J : ℝ,0 < J ∧ ∀ (Λ δ w K : ℝ) (hΛ : 1 ≤ Λ) (hδ : 0 < δ) (hw : 0 < w),
      w ≤ 1 → δ ≤ w → 0 ≤ K → ∀ (D : HeatDominatedKernel (C*w) K (by positivity))
      (f h : DyadicApproximation.RealL2) (M : ℝ),0 ≤ M →
      (∀ᵐ y ∂haarAddCircle,m ≤ (DyadicApproximation.realEmbed f y).re ∧
        (DyadicApproximation.realEmbed f y).re ≤ U) →
      (∀ᵐ y ∂haarAddCircle,m ≤ ((DyadicApproximation.realEmbed f+DyadicApproximation.realEmbed h) y).re ∧
        ((DyadicApproximation.realEmbed f+DyadicApproximation.realEmbed h) y).re ≤ U) →
      (∀ᵐ y ∂haarAddCircle,‖DyadicApproximation.realEmbed h y‖ ≤ M) →
      Summable (fun q : HaarNode => ‖separatedHeat Λ ρ δ hΛ hρ.le D.operator
        (globalColumnTaylorRemainder q (DyadicApproximation.realEmbed f) (DyadicApproximation.realEmbed h) j)‖^2) ∧
      (∑' q : HaarNode,‖separatedHeat Λ ρ δ hΛ hρ.le D.operator
        (globalColumnTaylorRemainder q (DyadicApproximation.realEmbed f) (DyadicApproximation.realEmbed h) j)‖^2) ≤
        (j.factorial:ℝ)⁻¹^2*J*K^2*w^(ρ-1/2)*δ^(-ρ)*(1+Real.log (w/δ))*
          StepInput.negativeEnergy 1 Λ ρ (DyadicApproximation.realEmbed h)*M^(2*j) := by
  obtain ⟨J,hJ,htrace⟩ := exists_global_scaled_envelope_trace m U hm j hρ hρhalf hC
  refine ⟨J,hJ,?_⟩
  intro Λ δ w K hΛ hδ hw hw1 hδw hK D f h M hM hf hfh hh
  let f' := DyadicApproximation.realEmbed f
  let h' := DyadicApproximation.realEmbed h
  let R := J*K^2*w^(ρ-1/2)*δ^(-ρ)*(1+Real.log (w/δ))*StepInput.negativeEnergy 1 Λ ρ h'*M^(2*j)
  have hE : 0 ≤ StepInput.negativeEnergy 1 Λ ρ h' := by
    rw [← NegativeNash.energy_eq_negativeEnergy Λ ρ (zero_lt_one.trans_le hΛ)]
    unfold NegativeNash.energy
    positivity
  have hlog : 0 ≤ Real.log (w/δ) := Real.log_nonneg ((one_le_div hδ).mpr hδw)
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hi := global_taylor_trace_transfer (separatedHeat Λ ρ δ hΛ hρ.le D.operator) f' h' m U hm hf hfh j R hR
    (fun r hr => by
      have he : DyadicApproximation.realEmbed (f+r•h) = f'+r•h' := by rw [map_add,map_smul]
      have hj := htrace Λ δ w K hΛ hδ hw hw1 hδw hK D (f+r•h) (by
        rw [he]
        exact affine_field_segment_bounds f' h' m U r hr hf hfh)
        (fun _ => h) (fun _ => M) (fun _ => hM) (fun _ _ => hh)
      simpa only [he,prod_const,card_erase_of_mem (mem_univ (0 : Fin (j+1))),card_univ,Fintype.card_fin,
        Nat.add_sub_cancel,R,f',h',show 2*j=j*2 by omega,← pow_mul] using! hj)
  exact ⟨hi.1,hi.2.trans_eq (by dsimp only [R,h']; ring)⟩

theorem exists_global_scaled_signed_trace (m U : ℝ) (hm : 0 < m)
    {ρ C : ℝ} (hρ : 0 < ρ) (hρhalf : ρ < 1/2) (hC : 0 < C) :
    ∃ J : ℝ,0 < J ∧ ∀ (Λ δ w K : ℝ) (hΛ : 1 ≤ Λ) (hδ : 0 < δ) (hw : 0 < w),
      w ≤ 1 → δ ≤ w → 0 ≤ K → ∀ (D : HeatDominatedKernel (C*w) K (by positivity))
      (f g : DyadicApproximation.RealL2),
      (∀ᵐ y ∂haarAddCircle,m ≤ (DyadicApproximation.realEmbed f y).re ∧
        (DyadicApproximation.realEmbed f y).re ≤ U) →
      (∀ᵐ y ∂haarAddCircle,m ≤ (DyadicApproximation.realEmbed g y).re ∧
        (DyadicApproximation.realEmbed g y).re ≤ U) →
      Summable (fun q : HaarNode => ‖separatedHeat Λ ρ δ hΛ hρ.le D.operator
        (globalHaarColumn q (DyadicApproximation.realEmbed g)-globalHaarColumn q (DyadicApproximation.realEmbed f))‖^2) ∧
      (∑' q : HaarNode,‖separatedHeat Λ ρ δ hΛ hρ.le D.operator
        (globalHaarColumn q (DyadicApproximation.realEmbed g)-globalHaarColumn q (DyadicApproximation.realEmbed f))‖^2) ≤
        J*K^2*w^(ρ-1/2)*δ^(-ρ)*(1+Real.log (w/δ))*
          StepInput.negativeEnergy 1 Λ ρ (DyadicApproximation.realEmbed (g-f)) := by
  obtain ⟨J,hJ,hTaylor⟩ := exists_global_scaled_taylor_trace m U hm 0 hρ hρhalf hC
  refine ⟨J,hJ,?_⟩
  intro Λ δ w K hΛ hδ hw hw1 hδw hK D f g hf hg
  have hU := elliptic_upper_nonneg (DyadicApproximation.realEmbed f) m U hm hf
  have he : DyadicApproximation.realEmbed f+DyadicApproximation.realEmbed (g-f) = DyadicApproximation.realEmbed g := by
    rw [map_sub]
    abel
  have hbound : ∀ᵐ y ∂haarAddCircle,‖DyadicApproximation.realEmbed (g-f) y‖ ≤ 2*U := by
    have he' : DyadicApproximation.realEmbed (g-f) = DyadicApproximation.realEmbed g-DyadicApproximation.realEmbed f := map_sub _ _ _
    rw [he']
    filter_upwards [Lp.coeFn_sub (DyadicApproximation.realEmbed g) (DyadicApproximation.realEmbed f),
      CircleMultiplier.elliptic_norm_bound _ m U hm (realEmbed_real f) hf,
      CircleMultiplier.elliptic_norm_bound _ m U hm (realEmbed_real g) hg] with y hy hfy hgy
    rw [hy]
    exact (norm_sub_le _ _).trans (by linarith)
  have hR (q : HaarNode) : globalColumnTaylorRemainder q (DyadicApproximation.realEmbed f)
      (DyadicApproximation.realEmbed (g-f)) 0 =
      globalHaarColumn q (DyadicApproximation.realEmbed g)-globalHaarColumn q (DyadicApproximation.realEmbed f) := by
    simp only [globalColumnTaylorRemainder,he,zero_add,range_one,sum_singleton,Nat.factorial_zero,
      Nat.cast_one,inv_one,iteratedFDeriv_zero_apply,one_smul]
  have hh := hTaylor Λ δ w K hΛ hδ hw hw1 hδw hK D f (g-f) (2*U) (by positivity) hf (by rw [he]; exact hg) hbound
  simpa only [hR,Nat.factorial_zero,Nat.cast_one,inv_one,one_pow,one_mul,mul_zero,pow_zero,mul_one] using! hh

end SHE.FiniteHaar
