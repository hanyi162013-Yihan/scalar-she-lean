module

public import SHE.HaarPacketL2
public import SHE.HaarTaylor

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section

namespace SHE.FiniteHaar
open Finset Set MeasureTheory AddCircle CircleHeat
local instance haarHigherHeat_periodPos : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩

theorem globalHaarColumn_jet_heat_packet {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1)
    (p : List Bool) (f : DyadicApproximation.RealL2)
    (hf : ∀ x, 0 < localAverage (p.length+1) (DyadicApproximation.realEmbed f) x)
    (j : ℕ) (v : Fin j → DyadicApproximation.RealL2) :
    ‖heat t (iteratedFDeriv ℝ j (globalHaarColumn (some p))
      (DyadicApproximation.realEmbed f) (fun i => DyadicApproximation.realEmbed (v i)))‖ ^ 2 ≤
      packetHeatConstant * min 1 ((nodeLength p) ^ 2 / t) *
        ‖iteratedFDeriv ℝ j (globalHaarColumn (some p))
          (DyadicApproximation.realEmbed f) (fun i => DyadicApproximation.realEmbed (v i))‖ ^ 2 :=
  supported_mean_zero_heat ht ht1 p _
    (globalHaarColumn_jet_supported p _ hf j _) (globalHaarColumn_jet_mean_zero p f hf j v)

/-- The literal generation of higher physical Haar derivative columns
has the same sharp heat cutoff as a mean-zero interval packet. Only the
distinguished direction uses `L²`; all other directions use their stated
essential bounds, with constants independent of the generation. -/
theorem globalHaarColumn_jet_heat_generation {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1)
    (n : ℕ) (f : DyadicApproximation.RealL2) (m U : ℝ) (hm : 0 < m)
    (hf : ∀ᵐ y ∂haarAddCircle, m ≤ (DyadicApproximation.realEmbed f y).re ∧
      (DyadicApproximation.realEmbed f y).re ≤ U)
    (j : ℕ) (v : Fin (j+1) → DyadicApproximation.RealL2) (M : Fin (j+1) → ℝ)
    (hM : ∀ i, 0 ≤ M i)
    (hv : ∀ i, i ≠ 0 → ∀ᵐ y ∂haarAddCircle, ‖DyadicApproximation.realEmbed (v i) y‖ ≤ M i) :
    (∑ x : Grid n, ‖heat t (iteratedFDeriv ℝ (j+1)
      (globalHaarColumn (some (leafPath n x))) (DyadicApproximation.realEmbed f)
        (fun i => DyadicApproximation.realEmbed (v i)))‖ ^ 2) ≤
      (2 * packetHeatConstant * (stateJetBound m U hm (j+1)) ^ 2 *
        ‖DyadicApproximation.realEmbed (v 0)‖ ^ 2 *
        (∏ i ∈ univ.erase (0 : Fin (j+1)), M i) ^ 2) *
      (((2 ^ (n+1) : ℕ) : ℝ)) * min 1 ((2 / (((2 ^ (n+1) : ℕ) : ℝ))) ^ 2 / t) := by
  have hpos (p : List Bool) (x : Grid (p.length+1)) :
      0 < localAverage (p.length+1) (DyadicApproximation.realEmbed f) x :=
    hm.trans_le (localAverage_bounds_ae _ _ m U hf x).1
  let A : ℝ := packetHeatConstant * min 1 ((2 / (((2 ^ (n+1) : ℕ) : ℝ))) ^ 2 / t)
  have hA : 0 ≤ A := mul_nonneg (zero_le_one.trans packetHeatConstant_one_le)
    (le_min zero_le_one (by positivity))
  calc
    _ ≤ ∑ x : Grid n, A * ‖iteratedFDeriv ℝ (j+1)
        (globalHaarColumn (some (leafPath n x))) (DyadicApproximation.realEmbed f)
          (fun i => DyadicApproximation.realEmbed (v i))‖ ^ 2 := by
      apply sum_le_sum
      intro x hx
      have hh := globalHaarColumn_jet_heat_packet ht ht1 (leafPath n x) f (hpos _) (j+1) v
      simpa only [nodeLength, leafPath_length, A] using hh
    _ = A * ∑ x : Grid n, ‖iteratedFDeriv ℝ (j+1)
        (globalHaarColumn (some (leafPath n x))) (DyadicApproximation.realEmbed f)
          (fun i => DyadicApproximation.realEmbed (v i))‖ ^ 2 := (mul_sum _ _ _).symm
    _ ≤ A * (2 * (stateJetBound m U hm (j+1)) ^ 2 * (((2 ^ (n+1) : ℕ) : ℝ)) *
        ‖DyadicApproximation.realEmbed (v 0)‖ ^ 2 *
        (∏ i ∈ univ.erase (0 : Fin (j+1)), M i) ^ 2) :=
      mul_le_mul_of_nonneg_left (globalHaarColumn_jet_generation_L2 n _ m U hm
        (realEmbed_real f) hf j _ M hM hv) hA
    _ = _ := by dsimp only [A]; ring

def pathLeaf : (p : List Bool) → Grid p.length
  | [] => ()
  | false :: p => Sum.inl (pathLeaf p)
  | true :: p => Sum.inr (pathLeaf p)

theorem leafPath_pathLeaf (p : List Bool) : leafPath p.length (pathLeaf p) = p := by
  induction p with
  | nil => rfl
  | cons b p ih => cases b <;> simp only [List.length_cons, pathLeaf, leafPath, ih]

/-- The actual local binary paths are enumerated once and only once by
their generations and physical dyadic cells. -/
def generationPathEquiv : (Σ n, Grid n) ≃ List Bool :=
  Equiv.ofBijective (fun nx => leafPath nx.1 nx.2) (by
    constructor
    · rintro ⟨n,x⟩ ⟨k,y⟩ h
      have he : n = k := by simpa only [leafPath_length] using congrArg List.length h
      subst k
      exact Sigma.ext rfl (heq_of_eq (leafPath_injective n h))
    · intro p
      exact ⟨⟨p.length,pathLeaf p⟩,leafPath_pathLeaf p⟩)

theorem packet_generation_sum {t C : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) (hC : 0 ≤ C)
    (F : List Bool → ℝ) (hF : ∀ p, 0 ≤ F p)
    (hgen : ∀ n, (∑ x : Grid n, F (leafPath n x)) ≤
      C * (((2 ^ (n+1) : ℕ) : ℝ)) * min 1 ((2 / (((2 ^ (n+1) : ℕ) : ℝ))) ^ 2 / t)) :
    Summable F ∧ (∑' p, F p) ≤
      2 * C * (DyadicTransport.smoothingConstant (1/2)) ^ 2 * t ^ (-(1/2 : ℝ)) := by
  let A : ℝ := t ^ (-(1/2 : ℝ))
  let s : ℕ → ℝ := DyadicTransport.smoothingTerm A (1/2)
  have hA : 1 ≤ A := by
    simpa only [A, Real.one_rpow] using Real.rpow_le_rpow_of_nonpos ht ht1 (by norm_num : -(1/2:ℝ) ≤ 0)
  have hs := DyadicTransport.smoothing_series hA (by norm_num : (0:ℝ)<1/2) (by norm_num : (1/2:ℝ)<1)
  have hs0 (n : ℕ) : 0 ≤ s n := by dsimp only [s, DyadicTransport.smoothingTerm]; positivity
  have hS0 : 0 ≤ ∑' n, s n := tsum_nonneg hs0
  have hsquare : Summable (fun n => s n ^ 2) := by
    apply Summable.of_nonneg_of_le (fun n => sq_nonneg (s n)) _ (hs.1.mul_left (∑' n, s n))
    intro n
    have hn : s n ≤ ∑' k, s k := hs.1.le_tsum n (fun k _ => hs0 k)
    nlinarith [mul_le_mul_of_nonneg_right hn (hs0 n)]
  have hsqsum : (∑' n, s n ^ 2) ≤ (∑' n, s n) ^ 2 := by
    calc
      _ ≤ ∑' n, (∑' k, s k) * s n := hsquare.tsum_le_tsum (fun n => by
        have hn : s n ≤ ∑' k, s k := hs.1.le_tsum n (fun k _ => hs0 k)
        nlinarith [mul_le_mul_of_nonneg_right hn (hs0 n)]) (hs.1.mul_left _)
      _ = _ := by rw [tsum_mul_left]; ring
  have hmajor (n : ℕ) : (∑ x : Grid n, F (leafPath n x)) ≤ 2 * C * s n ^ 2 := by
    let B : ℝ := (2:ℝ)^n
    let a : ℝ := A/B
    have hB : 0 < B := by dsimp [B]; positivity
    have ha : 0 ≤ a := by dsimp [a, A]; positivity
    have hN : (((2 ^ (n+1) : ℕ) : ℝ)) = 2*B := by
      norm_num only [Nat.cast_pow, Nat.cast_ofNat]
      rw [pow_succ]
      dsimp only [B]
      ring
    have hA2 : A ^ 2 = t⁻¹ := by
      dsimp only [A]
      rw [← Real.rpow_mul_natCast ht.le]
      norm_num only [Nat.cast_ofNat]
      rw [Real.rpow_neg_one]
    have he : (2 / (((2 ^ (n+1) : ℕ) : ℝ))) ^ 2 / t = a ^ 2 := by
      rw [hN]
      dsimp only [a]
      rw [div_pow, div_pow, hA2]
      field_simp [hB.ne', ht.ne']
    have hc : min 1 ((2 / (((2 ^ (n+1) : ℕ) : ℝ))) ^ 2 / t) ≤ (min 1 a) ^ 2 := by
      rw [he]
      by_cases ha1 : a ≤ 1
      · rw [min_eq_right ha1]
        exact min_le_right _ _
      · rw [min_eq_left (le_of_not_ge ha1), one_pow]
        exact min_le_left _ _
    have hsq : s n ^ 2 = (min 1 a) ^ 2 * B := by
      dsimp only [s, DyadicTransport.smoothingTerm, a, B]
      rw [mul_pow, ← Real.rpow_mul_natCast (by positivity : 0 ≤ (2:ℝ)^n)]
      norm_num
    exact (hgen n).trans ((mul_le_mul_of_nonneg_left hc (by positivity)).trans_eq (by rw [hsq,hN]; ring))
  have hE : Summable (fun n => ∑ x : Grid n, F (leafPath n x)) :=
    Summable.of_nonneg_of_le (fun n => sum_nonneg (fun x _ => hF _)) hmajor (hsquare.mul_left _)
  have hsig : Summable (fun nx : Σ n, Grid n => F (leafPath nx.1 nx.2)) := by
    apply (summable_sigma_of_nonneg (fun nx => hF _)).mpr
    exact ⟨fun n => (hasSum_fintype (fun x : Grid n => F (leafPath n x))).summable,
      by simpa only [tsum_fintype] using hE⟩
  have hsum : (∑' p, F p) = ∑' n, ∑ x : Grid n, F (leafPath n x) := by
    rw [← generationPathEquiv.tsum_eq F]
    simpa only [generationPathEquiv, Equiv.ofBijective_apply, tsum_fintype] using hsig.tsum_sigma
  refine ⟨generationPathEquiv.summable_iff.mp hsig, ?_⟩
  rw [hsum]
  calc
    _ ≤ ∑' n, 2*C*s n ^ 2 := hE.tsum_le_tsum hmajor (hsquare.mul_left _)
    _ = 2*C*(∑' n, s n ^ 2) := tsum_mul_left
    _ ≤ 2*C*(∑' n, s n) ^ 2 := mul_le_mul_of_nonneg_left hsqsum (by positivity)
    _ ≤ 2*C*(DyadicTransport.smoothingConstant (1/2)*A^(1/2:ℝ)) ^ 2 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hS0 hs.2 2) (by positivity)
    _ = _ := by
      rw [mul_pow, ← Real.rpow_mul_natCast (by positivity : 0 ≤ A)]
      norm_num only [Nat.cast_ofNat]
      rw [Real.rpow_one]
      dsimp only [A]
      ring

/-- The complete, countable family of genuine higher derivative detail
columns obeys the heat Hilbert--Schmidt bound with one `L²` direction.
All local mass, support, cancellation and generation estimates have
already been proved for the actual physical Haar construction. -/
theorem globalHaarColumn_higher_heat {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1)
    (f : DyadicApproximation.RealL2) (m U : ℝ) (hm : 0 < m)
    (hf : ∀ᵐ y ∂haarAddCircle, m ≤ (DyadicApproximation.realEmbed f y).re ∧
      (DyadicApproximation.realEmbed f y).re ≤ U)
    (j : ℕ) (v : Fin (j+1) → DyadicApproximation.RealL2) (M : Fin (j+1) → ℝ)
    (hM : ∀ i, 0 ≤ M i)
    (hv : ∀ i, i ≠ 0 → ∀ᵐ y ∂haarAddCircle, ‖DyadicApproximation.realEmbed (v i) y‖ ≤ M i) :
    Summable (fun p : List Bool => ‖heat t (iteratedFDeriv ℝ (j+1)
      (globalHaarColumn (some p)) (DyadicApproximation.realEmbed f)
        (fun i => DyadicApproximation.realEmbed (v i)))‖ ^ 2) ∧
    (∑' p : List Bool, ‖heat t (iteratedFDeriv ℝ (j+1)
      (globalHaarColumn (some p)) (DyadicApproximation.realEmbed f)
        (fun i => DyadicApproximation.realEmbed (v i)))‖ ^ 2) ≤
      (4 * packetHeatConstant * (stateJetBound m U hm (j+1)) ^ 2 *
        (DyadicTransport.smoothingConstant (1/2)) ^ 2) * t ^ (-(1/2:ℝ)) *
        ‖DyadicApproximation.realEmbed (v 0)‖ ^ 2 *
        (∏ i ∈ univ.erase (0 : Fin (j+1)), M i) ^ 2 := by
  have hP : 0 ≤ packetHeatConstant := zero_le_one.trans packetHeatConstant_one_le
  have hh := packet_generation_sum ht ht1
    (by positivity : 0 ≤ 2*packetHeatConstant*(stateJetBound m U hm (j+1))^2*
      ‖DyadicApproximation.realEmbed (v 0)‖^2*(∏ i ∈ univ.erase (0 : Fin (j+1)), M i)^2)
    (fun p : List Bool => ‖heat t (iteratedFDeriv ℝ (j+1)
      (globalHaarColumn (some p)) (DyadicApproximation.realEmbed f)
        (fun i => DyadicApproximation.realEmbed (v i)))‖ ^ 2)
    (fun _ => sq_nonneg _) (fun n => globalHaarColumn_jet_heat_generation ht ht1 n f m U hm hf j v M hM hv)
  exact ⟨hh.1, hh.2.trans_eq (by ring)⟩

end SHE.FiniteHaar
