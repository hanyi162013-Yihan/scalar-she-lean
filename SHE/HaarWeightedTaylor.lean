module

public import SHE.HaarWeightedHS

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section

namespace SHE.HaarWeightedHeat
open Finset Set MeasureTheory AddCircle CircleHeat FiniteHaar HeatMarkov NegativeNash
local instance haarWeightedTaylor_periodPos : Fact (0 < (1:ℝ)) := ⟨zero_lt_one⟩

/-- General transfer from genuine interval-supported mean-zero columns
to the massive weighted countable Hilbert--Schmidt bound. -/
theorem weighted_packet_family {Λ ρ t C : ℝ} (hΛ : 1 ≤ Λ) (hρ : 0 < ρ) (hρhalf : ρ < 1/2)
    (ht : 0 < t) (ht1 : t ≤ 1) (hC : 0 ≤ C)
    (w : List Bool → CircleL2)
    (hw : ∀ p, ∀ᵐ y ∂haarAddCircle, y ∉ nodeCell p → w p y = 0)
    (hz : ∀ p, inner ℂ circleOne (w p) = 0)
    (hgen : ∀ n, (∑ x : Grid n, ‖w (leafPath n x)‖^2) ≤ C*(((2^(n+1):ℕ):ℝ)))
    (b : CircleL2) (B : ℝ) (hB : 0 ≤ B) (hb : ∀ᵐ y ∂haarAddCircle, ‖b y‖ ≤ B) :
    Summable (fun p => ‖weightedHeat Λ ρ t hΛ hρ.le b B hb (w p)‖^2) ∧
    (∑' p, ‖weightedHeat Λ ρ t hΛ hρ.le b B hb (w p)‖^2) ≤
      2*packetConstant ρ*B^2*C*DyadicPowerSeries.constant (1-2*ρ) (2-4*ρ)*t^(ρ-1/2) := by
  have hP := packetConstant_nonneg hρhalf
  have hg (n : ℕ) : (∑ x : Grid n, ‖weightedHeat Λ ρ t hΛ hρ.le b B hb (w (leafPath n x))‖^2) ≤
      (packetConstant ρ*B^2*C)*(((2^(n+1):ℕ):ℝ))*(2/(((2^(n+1):ℕ):ℝ)))^(2*ρ)*
        (min 1 ((2/(((2^(n+1):ℕ):ℝ)))^2/t))^(1-2*ρ) := by
    let A := packetConstant ρ*B^2*(2/(((2^(n+1):ℕ):ℝ)))^(2*ρ)*
      (min 1 ((2/(((2^(n+1):ℕ):ℝ)))^2/t))^(1-2*ρ)
    have hA : 0 ≤ A := by dsimp only [A]; positivity
    calc
      _ ≤ ∑ x : Grid n, A*‖w (leafPath n x)‖^2 := by
        apply sum_le_sum
        intro x hx
        have hh := weighted_packet hΛ hρ hρhalf ht ht1 (leafPath n x) (w _) b B hB hb (hw _) (hz _)
        simpa only [weightedHeat,ContinuousLinearMap.comp_apply,nodeLength,leafPath_length,A] using hh
      _ = A*(∑ x : Grid n, ‖w (leafPath n x)‖^2) := (mul_sum _ _ _).symm
      _ ≤ A*(C*(((2^(n+1):ℕ):ℝ))) := mul_le_mul_of_nonneg_left (hgen n) hA
      _ = _ := by dsimp only [A]; ring
  have hh := weighted_packet_generation_sum ht ht1 hρ hρhalf
    (by positivity : 0 ≤ packetConstant ρ*B^2*C)
    (fun p => ‖weightedHeat Λ ρ t hΛ hρ.le b B hb (w p)‖^2) (fun _ => sq_nonneg _) hg
  exact ⟨hh.1,hh.2.trans_eq (by ring)⟩

theorem columnTaylorRemainder_generation_L2 (n : ℕ) (f h : CircleL2) (m U M : ℝ)
    (hm : 0 < m) (hM : 0 ≤ M)
    (hfreal : ∀ᵐ y ∂haarAddCircle, (f y).im = 0)
    (hhreal : ∀ᵐ y ∂haarAddCircle, (h y).im = 0)
    (hf : ∀ᵐ y ∂haarAddCircle, m ≤ (f y).re ∧ (f y).re ≤ U)
    (hfh : ∀ᵐ y ∂haarAddCircle, m ≤ ((f+h) y).re ∧ ((f+h) y).re ≤ U)
    (hh : ∀ᵐ y ∂haarAddCircle, ‖h y‖ ≤ M) (j : ℕ) :
    (∑ x : Grid n, ‖columnTaylorRemainder (leafPath n x) f h j‖^2) ≤
      (2*((j.factorial:ℝ)⁻¹*stateJetBound m U hm (j+1)*M^j)^2*‖h‖^2)*(((2^(n+1):ℕ):ℝ)) := by
  let D := ((j.factorial:ℝ)⁻¹*stateJetBound m U hm (j+1)*M^j)^2*(((2^(n+1):ℕ):ℝ))
  have hD : 0 ≤ D := by dsimp only [D]; positivity
  calc
    _ ≤ ∑ x : Grid n, D*localRestrictionNorm (leafPath n x) h^2 := by
      apply sum_le_sum
      intro x hx
      have hb := pow_le_pow_left₀ (norm_nonneg _) (columnTaylorRemainder_bound (leafPath n x)
        f h m U M hm hM hfreal hhreal hf hfh hh j) 2
      apply hb.trans_eq
      rw [leafPath_length]
      simp only [mul_pow,Real.sq_sqrt (by positivity : 0 ≤ (((2^(n+1):ℕ):ℝ)))]
      dsimp only [D]
      ring
    _ = D*∑ x : Grid n, localRestrictionNorm (leafPath n x) h^2 := (mul_sum _ _ _).symm
    _ ≤ D*(2*‖h‖^2) := mul_le_mul_of_nonneg_left (sum_localRestrictionNorm_sq n h) hD
    _ = _ := by dsimp only [D]; ring

/-- The exact first unified trace also holds for the actual integral
Taylor remainders at every finite order, with ellipticity only at the
two endpoints of the genuine coefficient segment. -/
theorem global_taylor_weighted_heat {Λ ρ t : ℝ} (hΛ : 1 ≤ Λ) (hρ : 0 < ρ) (hρhalf : ρ < 1/2)
    (ht : 0 < t) (ht1 : t ≤ 1) (f h : DyadicApproximation.RealL2) (m U M : ℝ)
    (hm : 0 < m) (hM : 0 ≤ M)
    (hf : ∀ᵐ y ∂haarAddCircle, m ≤ (DyadicApproximation.realEmbed f y).re ∧
      (DyadicApproximation.realEmbed f y).re ≤ U)
    (hfh : ∀ᵐ y ∂haarAddCircle, m ≤ ((DyadicApproximation.realEmbed f+DyadicApproximation.realEmbed h) y).re ∧
      ((DyadicApproximation.realEmbed f+DyadicApproximation.realEmbed h) y).re ≤ U)
    (hh : ∀ᵐ y ∂haarAddCircle, ‖DyadicApproximation.realEmbed h y‖ ≤ M)
    (j : ℕ) (b : CircleL2) (B : ℝ) (hB : 0 ≤ B) (hb : ∀ᵐ y ∂haarAddCircle, ‖b y‖ ≤ B) :
    Summable (fun q : HaarNode => ‖weightedHeat Λ ρ t hΛ hρ.le b B hb
      (globalColumnTaylorRemainder q (DyadicApproximation.realEmbed f) (DyadicApproximation.realEmbed h) j)‖^2) ∧
    (∑' q : HaarNode, ‖weightedHeat Λ ρ t hΛ hρ.le b B hb
      (globalColumnTaylorRemainder q (DyadicApproximation.realEmbed f) (DyadicApproximation.realEmbed h) j)‖^2) ≤
      (j.factorial:ℝ)⁻¹^2*higherConstant m U hm j ρ*B^2*t^(ρ-1/2)*
        ‖DyadicApproximation.realEmbed h‖^2*M^(2*j) := by
  let w : List Bool → CircleL2 := fun p => columnTaylorRemainder p
    (DyadicApproximation.realEmbed f) (DyadicApproximation.realEmbed h) j
  have hp (p : List Bool) (x : Grid (p.length+1)) :
      0 < localAverage (p.length+1) (DyadicApproximation.realEmbed f) x :=
    hm.trans_le (localAverage_bounds_ae _ _ m U hf x).1
  have hp' (p : List Bool) (x : Grid (p.length+1)) :
      0 < localAverage (p.length+1) (DyadicApproximation.realEmbed f+DyadicApproximation.realEmbed h) x :=
    hm.trans_le (localAverage_bounds_ae _ _ m U hfh x).1
  have hd := weighted_packet_family hΛ hρ hρhalf ht ht1
    (by positivity : 0 ≤ 2*((j.factorial:ℝ)⁻¹*stateJetBound m U hm (j+1)*M^j)^2*
      ‖DyadicApproximation.realEmbed h‖^2) w
    (fun p => columnTaylorRemainder_supported p _ _ j (hp p))
    (fun p => columnTaylorRemainder_mean_zero p f h (hp p) (hp' p) j)
    (fun n => columnTaylorRemainder_generation_L2 n _ _ m U M hm hM
      (realEmbed_real f) (realEmbed_real h) hf hfh hh j) b B hB hb
  let F : HaarNode → ℝ := fun q => ‖weightedHeat Λ ρ t hΛ hρ.le b B hb
    (globalColumnTaylorRemainder q (DyadicApproximation.realEmbed f) (DyadicApproximation.realEmbed h) j)‖^2
  have hsum := option_energy_sum F hd.1
  have htunit : 1 ≤ t^(ρ-1/2) := by
    simpa using Real.rpow_le_rpow_of_nonpos ht ht1 (by linarith : ρ-1/2 ≤ 0)
  have hc : F none ≤ (j.factorial:ℝ)⁻¹^2*(stateJetBound (m/2) U (by positivity) (j+1))^2*
      B^2*t^(ρ-1/2)*‖DyadicApproximation.realEmbed h‖^2*M^(2*j) := by
    have hn := pow_le_pow_left₀ (norm_nonneg _) (weightedHeat_norm_le Λ ρ t hΛ hρ.le b B hB hb
      (globalColumnTaylorRemainder none (DyadicApproximation.realEmbed f) (DyadicApproximation.realEmbed h) j)) 2
    rw [mul_pow] at hn
    have hj := pow_le_pow_left₀ (norm_nonneg _) (globalColumnTaylorRemainder_constant_bound
      _ _ m U M hm hM (realEmbed_real f) (realEmbed_real h) hf hfh hh j) 2
    apply (hn.trans (mul_le_mul_of_nonneg_left hj (sq_nonneg B))).trans
    simp only [mul_pow,← pow_mul]
    rw [show j*2 = 2*j by omega]
    have hs := mul_le_mul_of_nonneg_left htunit (by positivity :
      0 ≤ (j.factorial:ℝ)⁻¹^2*(stateJetBound (m/2) U (by positivity) (j+1))^2*
        B^2*‖DyadicApproximation.realEmbed h‖^2*M^(2*j))
    nlinarith only [hs]
  refine ⟨hsum.1, ?_⟩
  change (∑' q, F q) ≤ _
  rw [hsum.2]
  apply (add_le_add hd.2 hc).trans_eq
  unfold higherConstant
  rw [mul_pow,mul_pow,← pow_mul,show j*2 = 2*j by omega]
  ring

end SHE.HaarWeightedHeat
