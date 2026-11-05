module

public import SHE.HaarConstantJets

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section

namespace SHE.FiniteHaar
open Finset Set MeasureTheory AddCircle CircleHeat
local instance haarTaylorHeat_periodPos : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩

def globalColumnTaylorRemainder (q : HaarNode) (f h : CircleL2) (j : ℕ) : CircleL2 :=
  globalHaarColumn q (f+h) -
    ∑ k ∈ range (j+1), (k.factorial : ℝ)⁻¹ • iteratedFDeriv ℝ k (globalHaarColumn q) f (fun _ => h)

theorem globalColumnTaylorRemainder_some (p : List Bool) (f h : CircleL2) (j : ℕ) :
    globalColumnTaylorRemainder (some p) f h j = columnTaylorRemainder p f h j := rfl

theorem columnTaylorRemainder_mean_zero (p : List Bool) (f h : DyadicApproximation.RealL2)
    (hf : ∀ x, 0 < localAverage (p.length+1) (DyadicApproximation.realEmbed f) x)
    (hfh : ∀ x, 0 < localAverage (p.length+1)
      (DyadicApproximation.realEmbed f + DyadicApproximation.realEmbed h) x) (j : ℕ) :
    inner ℂ circleOne (columnTaylorRemainder p (DyadicApproximation.realEmbed f)
      (DyadicApproximation.realEmbed h) j) = 0 := by
  have hr : ∀ᵐ y ∂haarAddCircle,
      ((DyadicApproximation.realEmbed f + DyadicApproximation.realEmbed h) y).im = 0 := by
    rw [← map_add]
    exact realEmbed_real (f+h)
  unfold columnTaylorRemainder
  rw [inner_sub_right, globalHaarColumn_mean_zero p _ hr (hfh _) (hfh _), inner_sum]
  have hs : (∑ k ∈ range (j+1), inner ℂ circleOne ((k.factorial : ℝ)⁻¹ •
      iteratedFDeriv ℝ k (globalHaarColumn (some p)) (DyadicApproximation.realEmbed f)
        (fun _ => DyadicApproximation.realEmbed h))) = 0 := by
    apply sum_eq_zero
    intro k hk
    rw [inner_real_smul_right, globalHaarColumn_jet_mean_zero p f hf k (fun _ => h), mul_zero]
  rw [hs, sub_zero]

theorem globalColumnTaylorRemainder_constant_bound (f h : CircleL2) (m U M : ℝ)
    (hm : 0 < m) (hM : 0 ≤ M)
    (hfreal : ∀ᵐ y ∂haarAddCircle, (f y).im = 0)
    (hhreal : ∀ᵐ y ∂haarAddCircle, (h y).im = 0)
    (hf : ∀ᵐ y ∂haarAddCircle, m ≤ (f y).re ∧ (f y).re ≤ U)
    (hfh : ∀ᵐ y ∂haarAddCircle, m ≤ ((f+h) y).re ∧ ((f+h) y).re ≤ U)
    (hh : ∀ᵐ y ∂haarAddCircle, ‖h y‖ ≤ M) (j : ℕ) :
    ‖globalColumnTaylorRemainder none f h j‖ ≤ (j.factorial : ℝ)⁻¹ *
      stateJetBound (m/2) U (by positivity) (j+1) * ‖h‖ * M^j := by
  let C := stateJetBound (m/2) U (by positivity) (j+1) * ‖h‖ * M^j
  have hC : 0 ≤ C := mul_nonneg (mul_nonneg (stateJetBound_nonneg _ _ _ _) (norm_nonneg _)) (pow_nonneg hM _)
  have hpos (x : Grid 0) : 0 < localAverage 0 f x := hm.trans_le (localAverage_bounds_ae 0 f m U hf x).1
  have hpos' (x : Grid 0) : 0 < localAverage 0 (f+h) x := hm.trans_le (localAverage_bounds_ae 0 (f+h) m U hfh x).1
  unfold globalColumnTaylorRemainder
  rw [globalHaarColumn_taylor none f h j hpos hpos', add_sub_cancel_left, norm_smul]
  have hb : ∀ r ∈ uIoc (0:ℝ) 1, ‖(1-r)^j •
      iteratedFDeriv ℝ (j+1) (globalHaarColumn none) (f+r•h) (fun _ => h)‖ ≤ C := by
    intro r hr
    have hri : r ∈ Ioc (0:ℝ) 1 := by simpa only [uIoc_of_le zero_le_one] using hr
    have hr' : r ∈ Icc (0:ℝ) 1 := ⟨hri.1.le,hri.2⟩
    have hj := globalHaarColumn_constant_jet_bound (f+r•h) m U hm
      (affine_field_real f h r hfreal hhreal) (affine_field_segment_bounds f h m U r hr' hf hfh)
      j (fun _ => h) (fun _ => M) (fun _ => hM) (fun _ _ => hh)
    have hcard : (univ.erase (0 : Fin (j+1))).card = j := by simp
    simp only [prod_const, hcard] at hj
    have hp : ‖(1-r)^j‖ ≤ 1 := by
      rw [Real.norm_eq_abs, abs_pow, abs_of_nonneg (by linarith [hr'.2])]
      exact pow_le_one₀ (by linarith [hr'.2]) (by linarith [hr'.1])
    rw [norm_smul]
    exact (mul_le_mul hp hj (norm_nonneg _) zero_le_one).trans_eq (one_mul C)
  have hi : ‖∫ r in (0:ℝ)..1, (1-r)^j •
      iteratedFDeriv ℝ (j+1) (globalHaarColumn none) (f+r•h) (fun _ => h)‖ ≤ C := by
    simpa only [sub_zero, abs_one, mul_one] using intervalIntegral.norm_integral_le_of_norm_le_const hb
  exact (mul_le_mul_of_nonneg_left hi (norm_nonneg _)).trans_eq (by
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    dsimp only [C]
    ring)

/-- Integral Taylor remainders retain the quantitative countable packet
bound, with the additional bounded-direction power required by order. -/
theorem columnTaylorRemainder_heat {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1)
    (f h : DyadicApproximation.RealL2) (m U M : ℝ) (hm : 0 < m) (hM : 0 ≤ M)
    (hf : ∀ᵐ y ∂haarAddCircle, m ≤ (DyadicApproximation.realEmbed f y).re ∧
      (DyadicApproximation.realEmbed f y).re ≤ U)
    (hfh : ∀ᵐ y ∂haarAddCircle, m ≤ ((DyadicApproximation.realEmbed f + DyadicApproximation.realEmbed h) y).re ∧
      ((DyadicApproximation.realEmbed f + DyadicApproximation.realEmbed h) y).re ≤ U)
    (hh : ∀ᵐ y ∂haarAddCircle, ‖DyadicApproximation.realEmbed h y‖ ≤ M) (j : ℕ) :
    Summable (fun p : List Bool => ‖heat t (columnTaylorRemainder p
      (DyadicApproximation.realEmbed f) (DyadicApproximation.realEmbed h) j)‖ ^ 2) ∧
    (∑' p : List Bool, ‖heat t (columnTaylorRemainder p
      (DyadicApproximation.realEmbed f) (DyadicApproximation.realEmbed h) j)‖ ^ 2) ≤
      (4 * packetHeatConstant * (DyadicTransport.smoothingConstant (1/2)) ^ 2 *
        ((j.factorial : ℝ)⁻¹ * stateJetBound m U hm (j+1)) ^ 2) *
      t ^ (-(1/2:ℝ)) * ‖DyadicApproximation.realEmbed h‖ ^ 2 * M ^ (2*j) := by
  have hP : 0 ≤ packetHeatConstant := zero_le_one.trans packetHeatConstant_one_le
  let B := (j.factorial : ℝ)⁻¹ * stateJetBound m U hm (j+1) * M^j
  have hB : 0 ≤ B := mul_nonneg (mul_nonneg (by positivity) (stateJetBound_nonneg m U hm _)) (pow_nonneg hM _)
  have hp (p : List Bool) (x : Grid (p.length+1)) :
      0 < localAverage (p.length+1) (DyadicApproximation.realEmbed f) x :=
    hm.trans_le (localAverage_bounds_ae _ _ m U hf x).1
  have hp' (p : List Bool) (x : Grid (p.length+1)) :
      0 < localAverage (p.length+1) (DyadicApproximation.realEmbed f + DyadicApproximation.realEmbed h) x :=
    hm.trans_le (localAverage_bounds_ae _ _ m U hfh x).1
  have hgen (n : ℕ) : (∑ x : Grid n, ‖heat t (columnTaylorRemainder (leafPath n x)
      (DyadicApproximation.realEmbed f) (DyadicApproximation.realEmbed h) j)‖ ^ 2) ≤
      (2*packetHeatConstant*B^2*‖DyadicApproximation.realEmbed h‖^2) *
        (((2 ^ (n+1) : ℕ) : ℝ)) * min 1 ((2 / (((2 ^ (n+1) : ℕ) : ℝ))) ^ 2 / t) := by
    let A := packetHeatConstant * min 1 ((2 / (((2 ^ (n+1) : ℕ) : ℝ))) ^ 2 / t)
    have hA : 0 ≤ A := by dsimp [A]; positivity
    calc
      _ ≤ ∑ x : Grid n, (A*B^2*(((2 ^ (n+1) : ℕ) : ℝ))) *
          localRestrictionNorm (leafPath n x) (DyadicApproximation.realEmbed h)^2 := by
        apply sum_le_sum
        intro x hx
        have hheat := supported_mean_zero_heat ht ht1 (leafPath n x) _
          (columnTaylorRemainder_supported _ _ _ j (hp _))
          (columnTaylorRemainder_mean_zero _ f h (hp _) (hp' _) j)
        have hnorm := pow_le_pow_left₀ (norm_nonneg _)
          (columnTaylorRemainder_bound (leafPath n x) _ _ m U M hm hM
            (realEmbed_real f) (realEmbed_real h) hf hfh hh j) 2
        rw [nodeLength, leafPath_length] at hheat
        apply hheat.trans ((mul_le_mul_of_nonneg_left hnorm hA).trans_eq ?_)
        rw [leafPath_length]
        simp only [mul_pow, Real.sq_sqrt (by positivity : 0 ≤ (((2 ^ (n+1) : ℕ) : ℝ)))]
        dsimp only [A,B]
        ring
      _ = (A*B^2*(((2 ^ (n+1) : ℕ) : ℝ))) *
          ∑ x : Grid n, localRestrictionNorm (leafPath n x) (DyadicApproximation.realEmbed h)^2 :=
        (mul_sum _ _ _).symm
      _ ≤ (A*B^2*(((2 ^ (n+1) : ℕ) : ℝ))) * (2*‖DyadicApproximation.realEmbed h‖^2) :=
        mul_le_mul_of_nonneg_left (sum_localRestrictionNorm_sq n _) (by positivity)
      _ = _ := by dsimp only [A]; ring
  have hs := packet_generation_sum ht ht1 (by positivity : 0 ≤ 2*packetHeatConstant*B^2*‖DyadicApproximation.realEmbed h‖^2)
    (fun p => ‖heat t (columnTaylorRemainder p (DyadicApproximation.realEmbed f) (DyadicApproximation.realEmbed h) j)‖^2)
    (fun _ => sq_nonneg _) hgen
  refine ⟨hs.1, hs.2.trans_eq ?_⟩
  dsimp only [B]
  rw [mul_pow, ← pow_mul]
  rw [show j*2 = 2*j by omega]
  ring

/-- The full countable integral Taylor remainder, including the constant
column, is controlled in the actual heated Hilbert--Schmidt norm. -/
theorem globalColumnTaylorRemainder_heat {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1)
    (f h : DyadicApproximation.RealL2) (m U M : ℝ) (hm : 0 < m) (hM : 0 ≤ M)
    (hf : ∀ᵐ y ∂haarAddCircle, m ≤ (DyadicApproximation.realEmbed f y).re ∧
      (DyadicApproximation.realEmbed f y).re ≤ U)
    (hfh : ∀ᵐ y ∂haarAddCircle, m ≤ ((DyadicApproximation.realEmbed f + DyadicApproximation.realEmbed h) y).re ∧
      ((DyadicApproximation.realEmbed f + DyadicApproximation.realEmbed h) y).re ≤ U)
    (hh : ∀ᵐ y ∂haarAddCircle, ‖DyadicApproximation.realEmbed h y‖ ≤ M) (j : ℕ) :
    Summable (fun q : HaarNode => ‖heat t (globalColumnTaylorRemainder q
      (DyadicApproximation.realEmbed f) (DyadicApproximation.realEmbed h) j)‖ ^ 2) ∧
    (∑' q : HaarNode, ‖heat t (globalColumnTaylorRemainder q
      (DyadicApproximation.realEmbed f) (DyadicApproximation.realEmbed h) j)‖ ^ 2) ≤
      (j.factorial : ℝ)⁻¹ ^ 2 * higherHeatConstant m U hm j *
      t ^ (-(1/2:ℝ)) * ‖DyadicApproximation.realEmbed h‖ ^ 2 * M ^ (2*j) := by
  have hd := columnTaylorRemainder_heat ht ht1 f h m U M hm hM hf hfh hh j
  have hds : Summable (fun p : List Bool => ‖heat t (globalColumnTaylorRemainder (some p)
      (DyadicApproximation.realEmbed f) (DyadicApproximation.realEmbed h) j)‖^2) := hd.1
  have hsum := option_energy_sum (fun q : HaarNode => ‖heat t (globalColumnTaylorRemainder q
      (DyadicApproximation.realEmbed f) (DyadicApproximation.realEmbed h) j)‖^2) hds
  have htunit : 1 ≤ t ^ (-(1/2:ℝ)) := by
    simpa using Real.rpow_le_rpow_of_nonpos ht ht1 (by norm_num : -(1/2:ℝ) ≤ 0)
  have hc : ‖heat t (globalColumnTaylorRemainder none
      (DyadicApproximation.realEmbed f) (DyadicApproximation.realEmbed h) j)‖ ^ 2 ≤
      (j.factorial : ℝ)⁻¹ ^ 2 * (stateJetBound (m/2) U (by positivity) (j+1)) ^ 2 *
      t ^ (-(1/2:ℝ)) * ‖DyadicApproximation.realEmbed h‖ ^ 2 * M ^ (2*j) := by
    have hb := pow_le_pow_left₀ (norm_nonneg _) (globalColumnTaylorRemainder_constant_bound
      _ _ m U M hm hM (realEmbed_real f) (realEmbed_real h) hf hfh hh j) 2
    calc
      _ ≤ ‖globalColumnTaylorRemainder none (DyadicApproximation.realEmbed f)
          (DyadicApproximation.realEmbed h) j‖ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (heat_contraction t _) 2
      _ ≤ _ := hb.trans (by
        simp only [mul_pow, ← pow_mul]
        rw [show j*2 = 2*j by omega]
        have hs := mul_le_mul_of_nonneg_left htunit (by positivity :
          0 ≤ (j.factorial : ℝ)⁻¹ ^ 2 * (stateJetBound (m/2) U (by positivity) (j+1)) ^ 2 *
            ‖DyadicApproximation.realEmbed h‖ ^ 2 * M ^ (2*j))
        nlinarith only [hs])
  refine ⟨hsum.1, ?_⟩
  rw [hsum.2]
  exact (add_le_add hd.2 hc).trans_eq (by unfold higherHeatConstant; ring)

end SHE.FiniteHaar
