module

public import SHE.HaarWeightedHeat

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section

namespace SHE.HaarWeightedHeat
open Finset Set MeasureTheory AddCircle CircleHeat FiniteHaar HeatMarkov NegativeNash
local instance haarWeightedHS_periodPos : Fact (0 < (1:ℝ)) := ⟨zero_lt_one⟩

theorem min_square {a : ℝ} (ha : 0 ≤ a) : min 1 (a^2) = (min 1 a)^2 := by
  by_cases ha1 : a ≤ 1
  · rw [min_eq_right ha1, min_eq_right (by nlinarith : a^2 ≤ 1)]
  · rw [min_eq_left (le_of_not_ge ha1), min_eq_left (by nlinarith : 1 ≤ a^2), one_pow]

theorem packet_generation_weight_identity {t ρ : ℝ} (ht : 0 < t) (n : ℕ) :
    (((2 ^ (n+1) : ℕ) : ℝ)) * (2 / (((2 ^ (n+1) : ℕ) : ℝ)))^(2*ρ) *
      (min 1 ((2 / (((2 ^ (n+1) : ℕ) : ℝ)))^2/t))^(1-2*ρ) =
      2*DyadicPowerSeries.term (t^(-(1/2:ℝ))) (1-2*ρ) (2-4*ρ) n := by
  let B : ℝ := (2:ℝ)^n
  let A : ℝ := t^(-(1/2:ℝ))
  have hB : 0 < B := by dsimp [B]; positivity
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hN : (((2 ^ (n+1) : ℕ) : ℝ)) = 2*B := by
    norm_num only [Nat.cast_pow,Nat.cast_ofNat]
    rw [pow_succ]
    dsimp only [B]
    ring
  have hell : 2 / (((2 ^ (n+1) : ℕ) : ℝ)) = B⁻¹ := by rw [hN]; field_simp
  have hA2 : A^2 = t⁻¹ := by
    dsimp only [A]
    rw [← Real.rpow_mul_natCast ht.le]
    norm_num only [Nat.cast_ofNat]
    rw [Real.rpow_neg_one]
  have hratio : (2 / (((2 ^ (n+1) : ℕ) : ℝ)))^2/t = (A/B)^2 := by
    rw [hell, div_pow, hA2]
    field_simp
  rw [hratio,min_square (div_nonneg hA hB.le),← Real.rpow_natCast_mul (le_min zero_le_one (div_nonneg hA hB.le))]
  norm_num only [Nat.cast_ofNat]
  rw [show (2:ℝ)*(1-2*ρ) = 2-4*ρ by ring]
  have hp : (((2 ^ (n+1) : ℕ) : ℝ)) * (2 / (((2 ^ (n+1) : ℕ) : ℝ)))^(2*ρ) = 2*B^(1-2*ρ) := by
    rw [hell,hN,Real.inv_rpow hB.le,← Real.rpow_neg hB.le]
    calc
      _ = 2*(B^(1:ℝ)*B^(-(2*ρ))) := by rw [Real.rpow_one]; ring
      _ = _ := by rw [← Real.rpow_add hB]; congr 2
  rw [hp]
  unfold DyadicPowerSeries.term
  change 2*B^(1-2*ρ)*(min 1 (A/B))^(2-4*ρ) = 2*((min 1 (A/B))^(2-4*ρ)*B^(1-2*ρ))
  ring

theorem weighted_packet_generation_sum {t ρ C : ℝ} (ht : 0 < t) (ht1 : t ≤ 1)
    (_hρ : 0 < ρ) (hρhalf : ρ < 1/2) (hC : 0 ≤ C)
    (F : List Bool → ℝ) (hF : ∀ p, 0 ≤ F p)
    (hgen : ∀ n, (∑ x : Grid n, F (leafPath n x)) ≤
      C * (((2 ^ (n+1) : ℕ) : ℝ)) * (2 / (((2 ^ (n+1) : ℕ) : ℝ)))^(2*ρ) *
        (min 1 ((2 / (((2 ^ (n+1) : ℕ) : ℝ)))^2/t))^(1-2*ρ)) :
    Summable F ∧ (∑' p, F p) ≤
      2*C*DyadicPowerSeries.constant (1-2*ρ) (2-4*ρ)*t^(ρ-1/2) := by
  have hA : 1 ≤ t^(-(1/2:ℝ)) := by
    simpa using Real.rpow_le_rpow_of_nonpos ht ht1 (by norm_num : -(1/2:ℝ) ≤ 0)
  have hp : 0 < 1-2*ρ := by linarith
  have hpq : 1-2*ρ < 2-4*ρ := by linarith
  have hs := DyadicPowerSeries.series hA hp hpq
  have hmajor (n : ℕ) : (∑ x : Grid n, F (leafPath n x)) ≤
      (2*C)*DyadicPowerSeries.term (t^(-(1/2:ℝ))) (1-2*ρ) (2-4*ρ) n := by
    have he := packet_generation_weight_identity (ρ := ρ) ht n
    calc
      _ ≤ _ := hgen n
      _ = C*((((2 ^ (n+1) : ℕ) : ℝ)) * (2 / (((2 ^ (n+1) : ℕ) : ℝ)))^(2*ρ) *
          (min 1 ((2 / (((2 ^ (n+1) : ℕ) : ℝ)))^2/t))^(1-2*ρ)) := by ring
      _ = _ := by rw [he]; ring
  have hE : Summable (fun n => ∑ x : Grid n, F (leafPath n x)) :=
    Summable.of_nonneg_of_le (fun _ => sum_nonneg (fun _ _ => hF _)) hmajor (hs.1.mul_left _)
  have hsig : Summable (fun nx : Σ n, Grid n => F (leafPath nx.1 nx.2)) := by
    apply (summable_sigma_of_nonneg (fun nx => hF _)).mpr
    exact ⟨fun n => (hasSum_fintype (fun x : Grid n => F (leafPath n x))).summable,
      by simpa only [tsum_fintype] using hE⟩
  have hsum : (∑' p, F p) = ∑' n, ∑ x : Grid n, F (leafPath n x) := by
    rw [← generationPathEquiv.tsum_eq F]
    simpa only [generationPathEquiv,Equiv.ofBijective_apply,tsum_fintype] using hsig.tsum_sigma
  refine ⟨generationPathEquiv.summable_iff.mp hsig, ?_⟩
  rw [hsum]
  calc
    _ ≤ ∑' n, (2*C)*DyadicPowerSeries.term (t^(-(1/2:ℝ))) (1-2*ρ) (2-4*ρ) n :=
      hE.tsum_le_tsum hmajor (hs.1.mul_left _)
    _ = 2*C*(∑' n, DyadicPowerSeries.term (t^(-(1/2:ℝ))) (1-2*ρ) (2-4*ρ) n) := tsum_mul_left
    _ ≤ 2*C*(DyadicPowerSeries.constant (1-2*ρ) (2-4*ρ)*(t^(-(1/2:ℝ)))^(1-2*ρ)) :=
      mul_le_mul_of_nonneg_left hs.2 (by positivity)
    _ = _ := by rw [← Real.rpow_mul ht.le,show (-(1/2:ℝ))*(1-2*ρ) = ρ-1/2 by ring]; ring

def weightedHeat (Λ ρ t : ℝ) (hΛ : 1 ≤ Λ) (hρ : 0 ≤ ρ)
    (b : CircleL2) (B : ℝ) (hb : ∀ᵐ y ∂haarAddCircle, ‖b y‖ ≤ B) : CircleL2 →L[ℂ] CircleL2 :=
  (besselHalf Λ ρ hΛ hρ).comp ((CircleMultiplier.operator b B hb).comp (heat t))

theorem besselHalf_norm_le (Λ ρ : ℝ) (hΛ : 1 ≤ Λ) (hρ : 0 ≤ ρ) (f : CircleL2) :
    ‖besselHalf Λ ρ hΛ hρ f‖ ≤ ‖f‖ := by
  change ‖CircleNormalization.push.symm (OneInputOperator.besselHalf Λ ρ hΛ hρ
    (CircleNormalization.push f))‖ ≤ _
  rw [CircleNormalization.push.symm.norm_map]
  exact (OneInputOperator.besselHalf_norm_le Λ ρ hΛ hρ _).trans_eq (CircleNormalization.push.norm_map f)

theorem weightedHeat_norm_le (Λ ρ t : ℝ) (hΛ : 1 ≤ Λ) (hρ : 0 ≤ ρ)
    (b : CircleL2) (B : ℝ) (hB : 0 ≤ B) (hb : ∀ᵐ y ∂haarAddCircle, ‖b y‖ ≤ B)
    (f : CircleL2) : ‖weightedHeat Λ ρ t hΛ hρ b B hb f‖ ≤ B*‖f‖ :=
  (besselHalf_norm_le Λ ρ hΛ hρ _).trans ((CircleMultiplier.multiply_norm_le b B hb _).trans
    (mul_le_mul_of_nonneg_left (heat_contraction t f) hB))

def higherConstant (m U : ℝ) (hm : 0 < m) (j : ℕ) (ρ : ℝ) : ℝ :=
  4*packetConstant ρ*(stateJetBound m U hm (j+1))^2*
      DyadicPowerSeries.constant (1-2*ρ) (2-4*ρ) +
    (stateJetBound (m/2) U (by positivity) (j+1))^2

/-- The actual all-order one-`L²` unified trace, with a completely rough
bounded output multiplier and the massive Bessel half-operator. Every
column is the genuine Fréchet derivative of the same physical Haar factor;
the constant includes its constant mode and is independent of depth. -/
theorem global_higher_weighted_heat {Λ ρ t : ℝ} (hΛ : 1 ≤ Λ) (hρ : 0 < ρ) (hρhalf : ρ < 1/2)
    (ht : 0 < t) (ht1 : t ≤ 1) (f : DyadicApproximation.RealL2) (m U : ℝ) (hm : 0 < m)
    (hf : ∀ᵐ y ∂haarAddCircle, m ≤ (DyadicApproximation.realEmbed f y).re ∧
      (DyadicApproximation.realEmbed f y).re ≤ U)
    (j : ℕ) (v : Fin (j+1) → DyadicApproximation.RealL2) (M : Fin (j+1) → ℝ)
    (hM : ∀ i, 0 ≤ M i)
    (hv : ∀ i, i ≠ 0 → ∀ᵐ y ∂haarAddCircle, ‖DyadicApproximation.realEmbed (v i) y‖ ≤ M i)
    (b : CircleL2) (B : ℝ) (hB : 0 ≤ B) (hb : ∀ᵐ y ∂haarAddCircle, ‖b y‖ ≤ B) :
    Summable (fun q : HaarNode => ‖weightedHeat Λ ρ t hΛ hρ.le b B hb
      (iteratedFDeriv ℝ (j+1) (globalHaarColumn q) (DyadicApproximation.realEmbed f)
        (fun i => DyadicApproximation.realEmbed (v i)))‖^2) ∧
    (∑' q : HaarNode, ‖weightedHeat Λ ρ t hΛ hρ.le b B hb
      (iteratedFDeriv ℝ (j+1) (globalHaarColumn q) (DyadicApproximation.realEmbed f)
        (fun i => DyadicApproximation.realEmbed (v i)))‖^2) ≤
      higherConstant m U hm j ρ * B^2 * t^(ρ-1/2) * ‖DyadicApproximation.realEmbed (v 0)‖^2 *
        (∏ i ∈ univ.erase (0 : Fin (j+1)), M i)^2 := by
  have hP : 0 ≤ packetConstant ρ := packetConstant_nonneg hρhalf
  let F : HaarNode → ℝ := fun q => ‖weightedHeat Λ ρ t hΛ hρ.le b B hb
    (iteratedFDeriv ℝ (j+1) (globalHaarColumn q) (DyadicApproximation.realEmbed f)
      (fun i => DyadicApproximation.realEmbed (v i)))‖^2
  let C : ℝ := 2*packetConstant ρ*B^2*(stateJetBound m U hm (j+1))^2*
    ‖DyadicApproximation.realEmbed (v 0)‖^2*(∏ i ∈ univ.erase (0 : Fin (j+1)), M i)^2
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  have hp (p : List Bool) (x : Grid (p.length+1)) :
      0 < localAverage (p.length+1) (DyadicApproximation.realEmbed f) x :=
    hm.trans_le (localAverage_bounds_ae _ _ m U hf x).1
  have hgen (n : ℕ) : (∑ x : Grid n, F (some (leafPath n x))) ≤
      C * (((2 ^ (n+1) : ℕ) : ℝ)) * (2 / (((2 ^ (n+1) : ℕ) : ℝ)))^(2*ρ) *
        (min 1 ((2 / (((2 ^ (n+1) : ℕ) : ℝ)))^2/t))^(1-2*ρ) := by
    let A : ℝ := packetConstant ρ*B^2*(2 / (((2 ^ (n+1) : ℕ) : ℝ)))^(2*ρ)*
      (min 1 ((2 / (((2 ^ (n+1) : ℕ) : ℝ)))^2/t))^(1-2*ρ)
    have hA : 0 ≤ A := by dsimp only [A]; positivity
    calc
      _ ≤ ∑ x : Grid n, A*‖iteratedFDeriv ℝ (j+1) (globalHaarColumn (some (leafPath n x)))
          (DyadicApproximation.realEmbed f) (fun i => DyadicApproximation.realEmbed (v i))‖^2 := by
        apply sum_le_sum
        intro x hx
        have hh := weighted_packet hΛ hρ hρhalf ht ht1 (leafPath n x) _ b B hB hb
          (globalHaarColumn_jet_supported _ _ (hp _) (j+1) _)
          (globalHaarColumn_jet_mean_zero _ f (hp _) (j+1) v)
        simpa only [weightedHeat,ContinuousLinearMap.comp_apply,nodeLength,leafPath_length,F,A] using hh
      _ = A*(∑ x : Grid n, ‖iteratedFDeriv ℝ (j+1) (globalHaarColumn (some (leafPath n x)))
          (DyadicApproximation.realEmbed f) (fun i => DyadicApproximation.realEmbed (v i))‖^2) := (mul_sum _ _ _).symm
      _ ≤ A*(2*(stateJetBound m U hm (j+1))^2*(((2 ^ (n+1) : ℕ) : ℝ))*
          ‖DyadicApproximation.realEmbed (v 0)‖^2*(∏ i ∈ univ.erase (0 : Fin (j+1)), M i)^2) :=
        mul_le_mul_of_nonneg_left (globalHaarColumn_jet_generation_L2 n _ m U hm
          (realEmbed_real f) hf j _ M hM hv) hA
      _ = _ := by dsimp only [A,C]; ring
  have hd := weighted_packet_generation_sum ht ht1 hρ hρhalf hC (fun p => F (some p))
    (fun _ => sq_nonneg _) hgen
  have hsum := option_energy_sum F hd.1
  have htunit : 1 ≤ t^(ρ-1/2) := by
    simpa using Real.rpow_le_rpow_of_nonpos ht ht1 (by linarith : ρ-1/2 ≤ 0)
  have hc : F none ≤ B^2*(stateJetBound (m/2) U (by positivity) (j+1))^2*t^(ρ-1/2)*
      ‖DyadicApproximation.realEmbed (v 0)‖^2*(∏ i ∈ univ.erase (0 : Fin (j+1)), M i)^2 := by
    have hn := pow_le_pow_left₀ (norm_nonneg _) (weightedHeat_norm_le Λ ρ t hΛ hρ.le b B hB hb
      (iteratedFDeriv ℝ (j+1) (globalHaarColumn none) (DyadicApproximation.realEmbed f)
        (fun i => DyadicApproximation.realEmbed (v i)))) 2
    rw [mul_pow] at hn
    have hj := pow_le_pow_left₀ (norm_nonneg _) (globalHaarColumn_constant_jet_bound _ m U hm
      (realEmbed_real f) hf j _ M hM hv) 2
    have hc := hn.trans (mul_le_mul_of_nonneg_left hj (sq_nonneg B))
    apply hc.trans
    simp only [mul_pow]
    have hs := mul_le_mul_of_nonneg_left htunit (by positivity :
      0 ≤ B^2*(stateJetBound (m/2) U (by positivity) (j+1))^2*
        ‖DyadicApproximation.realEmbed (v 0)‖^2*(∏ i ∈ univ.erase (0 : Fin (j+1)), M i)^2)
    nlinarith only [hs]
  refine ⟨hsum.1, ?_⟩
  change (∑' q, F q) ≤ _
  rw [hsum.2]
  exact (add_le_add hd.2 hc).trans_eq (by unfold higherConstant; dsimp only [C]; ring)

end SHE.HaarWeightedHeat
