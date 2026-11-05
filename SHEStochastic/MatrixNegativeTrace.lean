module

public import SHEStochastic.MatrixNegativeGenerations
public import SHEStochastic.DyadicGenerationEnergy

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
noncomputable section

namespace SHEStochastic.MatrixNegativeTrace
open MeasureTheory SHE SHE.FiniteHaar SHE.DyadicApproximation SHE.HaarWeightedHeat SHE.CellNegative
open MatrixInfiniteHaar MatrixPhysicalColumnSmooth MatrixActualColumnCalculus MatrixProfileEntries MatrixNegativeEntries MatrixNegativeGenerations
open scoped NNReal ENNReal MatrixOrder Matrix.Norms.L2Operator
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local notation "μ" => AddCircle.haarAddCircle (T := (1 : ℝ))
variable {d : Type*} [Fintype d] [DecidableEq d]

def constant (P : Profile d) (ρ : ℝ) (hρ : 0 < ρ) (hρhalf : ρ < 1/2) (k : ℕ) : ℝ :=
  (coarseConstant P ρ hρ hρhalf k + fineConstant P ρ hρ hρhalf k) * NegativePacketSeries.constant ρ

theorem constant_pos (P : Profile d) (ρ : ℝ) (hρ : 0 < ρ) (hρhalf : ρ < 1/2) (k : ℕ) :
    0 < constant P ρ hρ hρhalf k :=
  mul_pos (add_pos (coarseConstant_pos P ρ hρ hρhalf k) (fineConstant_pos P ρ hρ hρhalf k)) (NegativePacketSeries.constant_pos hρhalf)

/-- The complete countable matrix detail family satisfies the sharp
negative-input, rough-output Hilbert--Schmidt heat trace at every order.
All local matrix calculus, localization, Gaussian packets and infinite
coarse/fine summation are conclusions of the imported checked chain. -/
theorem bound {Λ ρ t : ℝ} (hΛ : 1 ≤ Λ) (hρ : 0 < ρ) (hρhalf : ρ < 1/2) (ht : 0 < t) (ht1 : t ≤ 1)
    (P : Profile d) (v : Domain (d := d)) (w : List (Domain (d := d))) (M : Domain (d := d) → ℝ)
    (hM : ∀ q, 0 ≤ M q) (hRest : ∀ q ∈ w, ∀ᵐ x ∂μ, ‖q.val x‖ ≤ M q)
    (b : CircleHeat.CircleL2) (B : ℝ) (hB : 0 ≤ B) (hb : ∀ᵐ x ∂μ, ‖b x‖ ≤ B) :
    Summable (packetEnergy Λ ρ t hΛ hρ.le b B hb P v w) ∧
      (∑' p, packetEnergy Λ ρ t hΛ hρ.le b B hb P v w p) ≤
        constant P ρ hρ hρhalf w.length * B ^ 2 * t ^ (-(1/2 : ℝ)) *
          MatrixNegativeLocalization.energy Λ ρ v * MatrixJetClosure.weight M w ^ 2 := by
  let F := packetEnergy Λ ρ t hΛ hρ.le b B hb P v w
  let E := MatrixNegativeLocalization.energy Λ ρ v
  let W := MatrixJetClosure.weight M w
  let Cc := coarseConstant P ρ hρ hρhalf w.length
  let Cf := fineConstant P ρ hρ hρhalf w.length
  let C := (Cc+Cf)*B^2*E*W^2
  let g := fun n : ℕ => ∑ x : Grid n, F (leafPath n x)
  have hCc : 0 < Cc := coarseConstant_pos P ρ hρ hρhalf _
  have hCf : 0 < Cf := fineConstant_pos P ρ hρ hρhalf _
  have hE : 0 ≤ E := MatrixNegativeLocalization.energy_nonneg hΛ v
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hF : ∀ p, 0 ≤ F p := fun _ => Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _))
  have hg : ∀ n, 0 ≤ g n := fun _ => Finset.sum_nonneg (fun _ _ => hF _)
  have hc : ∀ n, (2 : ℝ)^n ≤ t^(-(1/2 : ℝ)) → g n ≤ C*t^(-ρ)*((2 : ℝ)^n)^(1-2*ρ) := by
    intro n hn
    have hh := coarse hΛ hρ hρhalf ht P n hn v w M hM hRest b B hB hb
    have hm := mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hCf.le : Cc ≤ Cc+Cf)
      (by positivity : 0 ≤ B^2*E*W^2*t^(-ρ)*((2 : ℝ)^n)^(1-2*ρ))
    exact hh.trans (by dsimp only [C,E,W]; nlinarith only [hm])
  have hf : ∀ n, t^(-(1/2 : ℝ)) ≤ (2 : ℝ)^n → g n ≤ C*t^(ρ-3/2)*((2 : ℝ)^n)^(2*ρ-2) := by
    intro n hn
    have hh := fine hΛ hρ hρhalf ht ht1 P n hn v w M hM hRest b B hB hb
    have hm := mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hCc.le : Cf ≤ Cc+Cf)
      (by positivity : 0 ≤ B^2*E*W^2*t^(ρ-3/2)*((2 : ℝ)^n)^(2*ρ-2))
    exact hh.trans (by dsimp only [C,E,W]; nlinarith only [hm])
  have hs := NegativePacketSeries.series hρhalf ht ht1 hC g hg hc hf
  have hp := DyadicGenerationEnergy.sum F hF hs.1
  refine ⟨hp.1, ?_⟩
  rw [hp.2]
  exact hs.2.trans_eq (by dsimp only [C,E,W,constant,Cc,Cf]; ring)

end SHEStochastic.MatrixNegativeTrace
