module

public import SHE.HaarNegativeGenerations

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1800000
noncomputable section

namespace SHE.FiniteHaar
open Finset Set MeasureTheory AddCircle CircleHeat HaarWeightedHeat
local instance haarNegativeTrace_periodPos : Fact (0 < (1:ℝ)) := ⟨zero_lt_one⟩

/-- The countable nonconstant Haar derivative trace with the actual
massive negative input norm and an arbitrary bounded rough output
multiplier. All local packets, disjoint negative localization and the
infinite coarse/fine sum are proved in the imported chain. -/
theorem exists_globalHaarColumn_jet_negative_trace (m U : ℝ) (hm : 0 < m) (j : ℕ)
    {ρ : ℝ} (hρ : 0 < ρ) (hρhalf : ρ < 1/2) :
    ∃ C : ℝ, 0 < C ∧ ∀ (Λ t : ℝ) (hΛ : 1 ≤ Λ) (ht : 0 < t), t ≤ 1 →
      ∀ (f : DyadicApproximation.RealL2),
      (∀ᵐ y ∂haarAddCircle, m ≤ (DyadicApproximation.realEmbed f y).re ∧
        (DyadicApproximation.realEmbed f y).re ≤ U) →
      ∀ (v : Fin (j+1) → DyadicApproximation.RealL2) (M : Fin (j+1) → ℝ),
      (∀ i, 0 ≤ M i) →
      (∀ i, i ≠ 0 → ∀ᵐ y ∂haarAddCircle, ‖DyadicApproximation.realEmbed (v i) y‖ ≤ M i) →
      ∀ (b : CircleL2) (B : ℝ) (hB : 0 ≤ B) (hb : ∀ᵐ y ∂haarAddCircle, ‖b y‖ ≤ B),
      Summable (negativeJetHeatEnergy Λ ρ t hΛ hρ.le b B hb f j v) ∧
      (∑' p : List Bool, negativeJetHeatEnergy Λ ρ t hΛ hρ.le b B hb f j v p) ≤
        C*B^2*t^(-(1/2:ℝ))*StepInput.negativeEnergy 1 Λ ρ (DyadicApproximation.realEmbed (v 0))*
          (∏ i ∈ univ.erase (0 : Fin (j+1)), M i)^2 := by
  obtain ⟨Cc,hCc,hcoarse⟩ := exists_coarse_negative_generation m U hm j hρ hρhalf
  obtain ⟨Cf,hCf,hfine⟩ := exists_fine_negative_generation m U hm j hρ hρhalf
  refine ⟨(Cc+Cf)*NegativePacketSeries.constant ρ,by positivity [NegativePacketSeries.constant_pos hρhalf],?_⟩
  intro Λ t hΛ ht ht1 f hf v M hM hv b B hB hb
  let F := negativeJetHeatEnergy Λ ρ t hΛ hρ.le b B hb f j v
  let E := StepInput.negativeEnergy 1 Λ ρ (DyadicApproximation.realEmbed (v 0))
  let P := ∏ i ∈ univ.erase (0 : Fin (j+1)), M i
  let C := (Cc+Cf)*B^2*E*P^2
  let g := fun n : ℕ => ∑ x : Grid n, F (leafPath n x)
  have hE : 0 ≤ E := by
    dsimp only [E]
    rw [← NegativeNash.energy_eq_negativeEnergy Λ ρ (zero_lt_one.trans_le hΛ)]
    unfold NegativeNash.energy
    positivity
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hF : ∀ p, 0 ≤ F p := fun _ => sq_nonneg _
  have hg : ∀ n, 0 ≤ g n := fun _ => sum_nonneg (fun _ _ => hF _)
  have hc : ∀ n, (2:ℝ)^n ≤ t^(-(1/2:ℝ)) → g n ≤ C*t^(-ρ)*((2:ℝ)^n)^(1-2*ρ) := by
    intro n hn
    have hh := hcoarse Λ t hΛ ht n hn f hf v M hM hv b B hB hb
    have hm := mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hCf.le : Cc ≤ Cc+Cf)
      (by positivity : 0 ≤ B^2*E*P^2*t^(-ρ)*((2:ℝ)^n)^(1-2*ρ))
    exact hh.trans (by dsimp only [C,E,P]; nlinarith only [hm])
  have hf' : ∀ n, t^(-(1/2:ℝ)) ≤ (2:ℝ)^n → g n ≤ C*t^(ρ-3/2)*((2:ℝ)^n)^(2*ρ-2) := by
    intro n hn
    have hh := hfine Λ t hΛ ht ht1 n hn f hf v M hM hv b B hB hb
    have hm := mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hCc.le : Cf ≤ Cc+Cf)
      (by positivity : 0 ≤ B^2*E*P^2*t^(ρ-3/2)*((2:ℝ)^n)^(2*ρ-2))
    exact hh.trans (by dsimp only [C,E,P]; nlinarith only [hm])
  have hs := NegativePacketSeries.series hρhalf ht ht1 hC g hg hc hf'
  have hsig : Summable (fun nx : Σ n, Grid n => F (leafPath nx.1 nx.2)) := by
    apply (summable_sigma_of_nonneg (fun nx => hF _)).mpr
    exact ⟨fun n => (hasSum_fintype (fun x : Grid n => F (leafPath n x))).summable,
      by simpa only [tsum_fintype] using hs.1⟩
  have he : (∑' p, F p) = ∑' n, g n := by
    rw [← generationPathEquiv.tsum_eq F]
    simpa only [generationPathEquiv,Equiv.ofBijective_apply,tsum_fintype] using hsig.tsum_sigma
  refine ⟨generationPathEquiv.summable_iff.mp hsig,?_⟩
  change (∑' p,F p) ≤ _
  rw [he]
  exact hs.2.trans_eq (by dsimp only [C,E,P]; ring)

end SHE.FiniteHaar
