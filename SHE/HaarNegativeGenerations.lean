module

public import SHE.NegativePacketScales
public import SHE.NegativePacketSeries

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 2500000
noncomputable section

namespace SHE.FiniteHaar
open Finset Set MeasureTheory AddCircle CircleHeat HeatMarkov HaarWeightedHeat CellNegative NegativeNash
local instance haarNegativeGenerations_periodPos : Fact (0 < (1:ℝ)) := ⟨zero_lt_one⟩

theorem nodeLength_leafPath (n : ℕ) (x : Grid n) :
    nodeLength (leafPath n x) = ((2:ℝ)^n)⁻¹ := by
  unfold nodeLength
  rw [leafPath_length]
  push_cast
  rw [pow_succ]
  field_simp

theorem coarse_generation_condition {t : ℝ} (ht : 0 < t) (n : ℕ)
    (hn : (2:ℝ)^n ≤ t^(-(1/2:ℝ))) : Real.sqrt t ≤ ((2:ℝ)^n)⁻¹ := by
  have hs : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht
  have hD : 0 < (2:ℝ)^n := by positivity
  have he : t^(-(1/2:ℝ)) = (Real.sqrt t)⁻¹ := by
    rw [Real.sqrt_eq_rpow,← Real.rpow_neg ht.le]
  rw [he] at hn
  have hh : (2:ℝ)^n*Real.sqrt t ≤ 1 := (le_div_iff₀ hs).mp (by simpa only [one_div] using hn)
  rw [inv_eq_one_div]
  apply (le_div_iff₀ hD).mpr
  nlinarith only [hh]

theorem fine_generation_condition {t : ℝ} (ht : 0 < t) (n : ℕ)
    (hn : t^(-(1/2:ℝ)) ≤ (2:ℝ)^n) : ((2:ℝ)^n)⁻¹ ≤ Real.sqrt t := by
  have hs : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht
  have hD : 0 < (2:ℝ)^n := by positivity
  have he : t^(-(1/2:ℝ)) = (Real.sqrt t)⁻¹ := by
    rw [Real.sqrt_eq_rpow,← Real.rpow_neg ht.le]
  rw [he] at hn
  have hh : 1 ≤ (2:ℝ)^n*Real.sqrt t := (div_le_iff₀ hs).mp (by simpa only [one_div] using hn)
  rw [inv_eq_one_div]
  apply (div_le_iff₀ hD).mpr
  nlinarith only [hh]

def negativeJetHeatEnergy (Λ ρ t : ℝ) (hΛ : 1 ≤ Λ) (hρ : 0 ≤ ρ)
    (b : CircleL2) (B : ℝ) (hb : ∀ᵐ y ∂haarAddCircle, ‖b y‖ ≤ B)
    (f : DyadicApproximation.RealL2) (j : ℕ) (v : Fin (j+1) → DyadicApproximation.RealL2)
    (p : List Bool) : ℝ :=
  ‖weightedHeat Λ ρ t hΛ hρ b B hb
    (iteratedFDeriv ℝ (j+1) (globalHaarColumn (some p)) (DyadicApproximation.realEmbed f)
      (fun i => DyadicApproximation.realEmbed (v i)))‖^2

theorem exists_coarse_negative_generation (m U : ℝ) (hm : 0 < m) (j : ℕ)
    {ρ : ℝ} (hρ : 0 < ρ) (hρhalf : ρ < 1/2) :
    ∃ C : ℝ, 0 < C ∧ ∀ (Λ t : ℝ) (hΛ : 1 ≤ Λ) (ht : 0 < t) (n : ℕ),
      (2:ℝ)^n ≤ t^(-(1/2:ℝ)) → ∀ (f : DyadicApproximation.RealL2),
      (∀ᵐ y ∂haarAddCircle, m ≤ (DyadicApproximation.realEmbed f y).re ∧
        (DyadicApproximation.realEmbed f y).re ≤ U) →
      ∀ (v : Fin (j+1) → DyadicApproximation.RealL2) (M : Fin (j+1) → ℝ),
      (∀ i, 0 ≤ M i) →
      (∀ i, i ≠ 0 → ∀ᵐ y ∂haarAddCircle, ‖DyadicApproximation.realEmbed (v i) y‖ ≤ M i) →
      ∀ (b : CircleL2) (B : ℝ) (hB : 0 ≤ B) (hb : ∀ᵐ y ∂haarAddCircle, ‖b y‖ ≤ B),
      (∑ x : Grid n, negativeJetHeatEnergy Λ ρ t hΛ hρ.le b B hb f j v (leafPath n x)) ≤
        C*B^2*StepInput.negativeEnergy 1 Λ ρ (DyadicApproximation.realEmbed (v 0))*
          (∏ i ∈ univ.erase (0 : Fin (j+1)), M i)^2*t^(-ρ)*((2:ℝ)^n)^(1-2*ρ) := by
  obtain ⟨K,hK,hgen⟩ := exists_globalHaarColumn_jet_negative_generation_bound m U hm j hρ hρhalf
  let C := 4*HaarNegativeCoarse.constant ρ*K
  have hCc : 0 < HaarNegativeCoarse.constant ρ := zero_lt_one.trans_le (HaarNegativeCoarse.constant_one_le ρ)
  refine ⟨C,by dsimp [C]; positivity,?_⟩
  intro Λ t hΛ ht n hn f hf v M hM hv b B hB hb
  let D : ℝ := (2:ℝ)^n
  let N : ℝ := ((2^(n+1):ℕ):ℝ)
  let T := (Λ^ρ+t^(-ρ))*min (Λ^(-ρ)) (N^(-2*ρ))
  let E := StepInput.negativeEnergy 1 Λ ρ (DyadicApproximation.realEmbed (v 0))
  let P := ∏ i ∈ univ.erase (0 : Fin (j+1)), M i
  let a := HaarNegativeCoarse.constant ρ*B^2*T
  have hN : N = 2*D := by dsimp [N,D]; push_cast; rw [pow_succ]; ring
  have ha : 0 ≤ a := by dsimp [a,T]; positivity
  have hE : 0 ≤ E := by
    dsimp only [E]
    rw [← energy_eq_negativeEnergy Λ ρ (zero_lt_one.trans_le hΛ)]
    unfold energy
    positivity
  have hfinite : (∑ x : Grid n, negativeJetHeatEnergy Λ ρ t hΛ hρ.le b B hb f j v (leafPath n x)) ≤
      a*(K*N*E*P^2) := by
    calc
      _ ≤ ∑ x : Grid n, a*‖besselHalf Λ ρ hΛ hρ.le
          (iteratedFDeriv ℝ (j+1) (globalHaarColumn (some (leafPath n x))) (DyadicApproximation.realEmbed f)
            (fun i => DyadicApproximation.realEmbed (v i)))‖^2 := by
        apply sum_le_sum
        intro x _
        have hp (y : Grid ((leafPath n x).length+1)) : 0 < localAverage ((leafPath n x).length+1) (DyadicApproximation.realEmbed f) y :=
          hm.trans_le (localAverage_bounds_ae _ _ m U hf y).1
        let w := iteratedFDeriv ℝ (j+1) (globalHaarColumn (some (leafPath n x))) (DyadicApproximation.realEmbed f)
          (fun i => DyadicApproximation.realEmbed (v i))
        have hh := HaarNegativeCoarse.packet hΛ hρ hρhalf ht (leafPath n x)
          (by rw [nodeLength_leafPath]; exact coarse_generation_condition ht n hn)
          w (globalHaarColumn_jet_supported (leafPath n x) _ hp (j+1) _) b B hB hb
        rw [← besselHalf_norm_sq _ _ hΛ hρ.le] at hh
        simpa only [negativeJetHeatEnergy,leafPath_length,a,T,N,mul_assoc] using! hh
      _ = a*∑ x : Grid n, ‖besselHalf Λ ρ hΛ hρ.le
          (iteratedFDeriv ℝ (j+1) (globalHaarColumn (some (leafPath n x))) (DyadicApproximation.realEmbed f)
            (fun i => DyadicApproximation.realEmbed (v i)))‖^2 := (mul_sum _ _ _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (hgen Λ hΛ n _ (realEmbed_real f) hf (fun i => DyadicApproximation.realEmbed (v i)) M hM hv) ha
  have hs := NegativePacketScales.coarse_mass_mesh (zero_lt_one.trans_le hΛ) hρ.le ht
    (by positivity : 0 < (2:ℝ)^n) (coarse_generation_condition ht n hn)
  have hs' : T*N ≤ 4*t^(-ρ)*D^(1-2*ρ) := by simpa only [T,hN] using hs
  have hh := mul_le_mul_of_nonneg_left hs' (by positivity : 0 ≤ HaarNegativeCoarse.constant ρ*B^2*K*E*P^2)
  exact hfinite.trans (by dsimp only [a,C,D]; nlinarith only [hh])

theorem exists_fine_negative_generation (m U : ℝ) (hm : 0 < m) (j : ℕ)
    {ρ : ℝ} (hρ : 0 < ρ) (hρhalf : ρ < 1/2) :
    ∃ C : ℝ, 0 < C ∧ ∀ (Λ t : ℝ) (hΛ : 1 ≤ Λ) (ht : 0 < t), t ≤ 1 → ∀ (n : ℕ),
      t^(-(1/2:ℝ)) ≤ (2:ℝ)^n → ∀ (f : DyadicApproximation.RealL2),
      (∀ᵐ y ∂haarAddCircle, m ≤ (DyadicApproximation.realEmbed f y).re ∧
        (DyadicApproximation.realEmbed f y).re ≤ U) →
      ∀ (v : Fin (j+1) → DyadicApproximation.RealL2) (M : Fin (j+1) → ℝ),
      (∀ i, 0 ≤ M i) →
      (∀ i, i ≠ 0 → ∀ᵐ y ∂haarAddCircle, ‖DyadicApproximation.realEmbed (v i) y‖ ≤ M i) →
      ∀ (b : CircleL2) (B : ℝ) (hB : 0 ≤ B) (hb : ∀ᵐ y ∂haarAddCircle, ‖b y‖ ≤ B),
      (∑ x : Grid n, negativeJetHeatEnergy Λ ρ t hΛ hρ.le b B hb f j v (leafPath n x)) ≤
        C*B^2*StepInput.negativeEnergy 1 Λ ρ (DyadicApproximation.realEmbed (v 0))*
          (∏ i ∈ univ.erase (0 : Fin (j+1)), M i)^2*t^(ρ-3/2)*((2:ℝ)^n)^(2*ρ-2) := by
  obtain ⟨K,hK,hloc⟩ := exists_sum_localNegativeNorm_bound hρ hρhalf
  let A := negativeFineConstant m U hm j ρ
  have hA : 0 ≤ A := by
    dsimp [A,negativeFineConstant,GaussianNegativePacket.constant]
    have hG := (HeatTrace.fractionalGaussianIntegral_pos hρhalf).le
    positivity [GaussianNegativePacket.traceConstant_pos]
  let C := 1+2*A*K
  refine ⟨C,by dsimp [C]; positivity,?_⟩
  intro Λ t hΛ ht ht1 n hn f hf v M hM hv b B hB hb
  let D : ℝ := (2:ℝ)^n
  let N : ℝ := ((2^(n+1):ℕ):ℝ)
  let E := StepInput.negativeEnergy 1 Λ ρ (DyadicApproximation.realEmbed (v 0))
  let P := ∏ i ∈ univ.erase (0 : Fin (j+1)), M i
  let T := t^(ρ-3/2)*D^(2*ρ-2)
  have hN : N = 2*D := by dsimp [N,D]; push_cast; rw [pow_succ]; ring
  have hD : 0 < D := by dsimp [D]; positivity
  have hE : 0 ≤ E := by
    dsimp only [E]
    rw [← energy_eq_negativeEnergy Λ ρ (zero_lt_one.trans_le hΛ)]
    unfold energy
    positivity
  have hD2 : t⁻¹ ≤ D^2 := by
    have hh := pow_le_pow_left₀ (by positivity : 0 ≤ t^(-(1/2:ℝ))) hn 2
    rw [← Real.rpow_mul_natCast ht.le] at hh
    norm_num only [Nat.cast_ofNat,neg_mul,one_div,inv_mul_cancel₀ (by norm_num : (2:ℝ) ≠ 0),one_mul,Real.rpow_neg_one] at hh
    exact hh
  have hNt : t⁻¹ ≤ N^2 := hD2.trans (by rw [hN]; nlinarith [sq_nonneg D])
  have hs := NegativePacketScales.fine_mass_mesh (zero_lt_one.trans_le hΛ) hρ.le (by linarith : ρ ≤ 1)
    ht (by rw [hN]; positivity) hNt
  have hpower : N^(2*ρ-2) ≤ D^(2*ρ-2) :=
    Real.rpow_le_rpow_of_nonpos hD (by rw [hN]; linarith) (by linarith)
  have hs' : N⁻¹^2*t⁻¹*(Λ+N^2)^ρ*min (Λ^(-ρ)*t^(-(1/2:ℝ))) (t^(ρ-1/2)) ≤ 2*T := by
    exact hs.trans (by dsimp only [T]; nlinarith [mul_le_mul_of_nonneg_left hpower (by positivity : 0 ≤ 2*t^(ρ-3/2))])
  have hfinite : (∑ x : Grid n, negativeJetHeatEnergy Λ ρ t hΛ hρ.le b B hb f j v (leafPath n x)) ≤
      (2*A*B^2*T*P^2)*(K*E) := by
    calc
      _ ≤ ∑ x : Grid n, (2*A*B^2*T*P^2)*
          localNegativeNorm (leafPath n x) Λ ρ hΛ hρ.le (DyadicApproximation.realEmbed (v 0))^2 := by
        apply sum_le_sum
        intro x _
        have hh := globalHaarColumn_jet_fine_negative hΛ hρ hρhalf ht ht1 (leafPath n x)
          (by rw [nodeLength_leafPath]; exact fine_generation_condition ht n hn) f m U hm hf j v M hM hv b B hB hb
        rw [leafPath_length] at hh
        have hsx := mul_le_mul_of_nonneg_left hs' (by positivity : 0 ≤ A*B^2*
          localNegativeNorm (leafPath n x) Λ ρ hΛ hρ.le (DyadicApproximation.realEmbed (v 0))^2*P^2)
        exact hh.trans (by dsimp only [negativeJetHeatEnergy,A,N,P]; nlinarith only [hsx])
      _ = (2*A*B^2*T*P^2)*∑ x : Grid n,
          localNegativeNorm (leafPath n x) Λ ρ hΛ hρ.le (DyadicApproximation.realEmbed (v 0))^2 := (mul_sum _ _ _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left (hloc Λ hΛ n (DyadicApproximation.realEmbed (v 0))) (by dsimp [T]; positivity)
  have hc : 2*A*K ≤ C := by dsimp [C]; linarith
  have hmul := mul_le_mul_of_nonneg_right hc (by dsimp [T]; positivity : 0 ≤ B^2*E*P^2*T)
  exact hfinite.trans (by dsimp only [T,C,D]; nlinarith only [hmul])

end SHE.FiniteHaar
