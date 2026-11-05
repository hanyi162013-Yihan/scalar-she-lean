module

public import SHE.HaarFineL1Negative
public import SHE.SeparatedPacketScales
public import SHE.HaarNegativeGenerations
public import SHE.HeatDominatedCoarse
public import SHE.HeatDominatedNegative

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 2500000
noncomputable section

namespace SHE
open MeasureTheory AddCircle CircleHeat HeatMarkov
local instance haarSeparatedKernel_periodPos : Fact (0 < (1:ℝ)) := ⟨zero_lt_one⟩

/-- A literal measurable spatial integral kernel and its bounded L²
operator. The only kernel estimate is the stated pointwise Gaussian
envelope; no Schur, Sobolev or trace estimate is a field. -/
structure HeatDominatedKernel (w K : ℝ) (hw : 0 < w) where
  operator : CircleL2 →L[ℂ] CircleL2
  kernel : AddCircle (1:ℝ) × AddCircle (1:ℝ) → ℂ
  measurable_kernel : Measurable kernel
  kernel_bound : ∀ x y,‖kernel (x,y)‖ ≤ K*‖HeatMarkov.kernel w hw (y-x)‖
  representation : ∀ f : CircleL2,operator f =ᵐ[haarAddCircle]
    (fun x => ∫ y : AddCircle (1:ℝ),kernel (x,y)*f y ∂haarAddCircle)

namespace FiniteHaar
open Finset Set HaarWeightedHeat CellNegative NegativeNash

def separatedJetEnergy {w K : ℝ} {hw : 0 < w} (D : HeatDominatedKernel w K hw)
    (Λ ρ δ : ℝ) (f : DyadicApproximation.RealL2) (j : ℕ)
    (v : Fin (j+1) → DyadicApproximation.RealL2) (p : List Bool) : ℝ :=
  energy Λ ρ (D.operator (heat δ (iteratedFDeriv ℝ (j+1) (globalHaarColumn (some p))
    (DyadicApproximation.realEmbed f) (fun i => DyadicApproximation.realEmbed (v i)))))

theorem exists_separated_coarse_generation (m U : ℝ) (hm : 0 < m) (j : ℕ)
    {ρ : ℝ} (hρ : 0 < ρ) (hρhalf : ρ < 1/2) :
    ∃ C : ℝ, 0 < C ∧ ∀ (Λ δ w K : ℝ) (hΛ : 1 ≤ Λ) (hδ : 0 < δ) (hw : 0 < w),
      δ ≤ w → 0 ≤ K → ∀ (D : HeatDominatedKernel w K hw) (n : ℕ),
      (2:ℝ)^n ≤ w^(-(1/2:ℝ)) → ∀ (f : DyadicApproximation.RealL2),
      (∀ᵐ y ∂haarAddCircle, m ≤ (DyadicApproximation.realEmbed f y).re ∧
        (DyadicApproximation.realEmbed f y).re ≤ U) →
      ∀ (v : Fin (j+1) → DyadicApproximation.RealL2) (M : Fin (j+1) → ℝ),
      (∀ i, 0 ≤ M i) →
      (∀ i, i ≠ 0 → ∀ᵐ y ∂haarAddCircle, ‖DyadicApproximation.realEmbed (v i) y‖ ≤ M i) →
      (∑ x : Grid n,separatedJetEnergy D Λ ρ δ f j v (leafPath n x)) ≤
        C*K^2*StepInput.negativeEnergy 1 Λ ρ (DyadicApproximation.realEmbed (v 0))*
          (∏ i ∈ univ.erase (0 : Fin (j+1)), M i)^2*δ^(-ρ)*((2:ℝ)^n)^(1-2*ρ) := by
  obtain ⟨J,hJ,hgen⟩ := exists_globalHaarColumn_jet_negative_generation_bound m U hm j hρ hρhalf
  let C := 4*HaarNegativeCoarse.constant ρ*J
  have hCc : 0 < HaarNegativeCoarse.constant ρ := zero_lt_one.trans_le (HaarNegativeCoarse.constant_one_le ρ)
  refine ⟨C,by dsimp [C]; positivity,?_⟩
  intro Λ δ w K hΛ hδ hw hδw hK D n hn f hf v M hM hv
  let L : ℝ := (2:ℝ)^n
  let N : ℝ := ((2^(n+1):ℕ):ℝ)
  let T := (Λ^ρ+δ^(-ρ))*min (Λ^(-ρ)) (N^(-2*ρ))
  let E := StepInput.negativeEnergy 1 Λ ρ (DyadicApproximation.realEmbed (v 0))
  let P := ∏ i ∈ univ.erase (0 : Fin (j+1)), M i
  let a := HaarNegativeCoarse.constant ρ*K^2*T
  have hN : N = 2*L := by dsimp [N,L]; push_cast; rw [pow_succ]; ring
  have ha : 0 ≤ a := by dsimp [a,T]; positivity
  have hE : 0 ≤ E := by
    dsimp only [E]
    rw [← energy_eq_negativeEnergy Λ ρ (zero_lt_one.trans_le hΛ)]
    unfold energy
    positivity
  have hc : Real.sqrt δ ≤ ((2:ℝ)^n)⁻¹ :=
    (Real.sqrt_le_sqrt hδw).trans (coarse_generation_condition hw n hn)
  have hfinite : (∑ x : Grid n,separatedJetEnergy D Λ ρ δ f j v (leafPath n x)) ≤
      a*(J*N*E*P^2) := by
    calc
      _ ≤ ∑ x : Grid n,a*‖besselHalf Λ ρ hΛ hρ.le
          (iteratedFDeriv ℝ (j+1) (globalHaarColumn (some (leafPath n x))) (DyadicApproximation.realEmbed f)
            (fun i => DyadicApproximation.realEmbed (v i)))‖^2 := by
        apply sum_le_sum
        intro x _
        have hp (y : Grid ((leafPath n x).length+1)) : 0 < localAverage ((leafPath n x).length+1) (DyadicApproximation.realEmbed f) y :=
          hm.trans_le (localAverage_bounds_ae _ _ m U hf y).1
        let z := iteratedFDeriv ℝ (j+1) (globalHaarColumn (some (leafPath n x))) (DyadicApproximation.realEmbed f)
          (fun i => DyadicApproximation.realEmbed (v i))
        have hh := HeatDominatedCoarse.packet hw hK D.operator D.kernel D.measurable_kernel D.kernel_bound D.representation
          hΛ hρ hρhalf hδ (leafPath n x) (by rw [nodeLength_leafPath]; exact hc)
          z (globalHaarColumn_jet_supported (leafPath n x) _ hp (j+1) _)
        rw [← besselHalf_norm_sq Λ ρ hΛ hρ.le z] at hh
        simpa only [separatedJetEnergy,leafPath_length,a,T,N,mul_assoc] using! hh
      _ = a*∑ x : Grid n,‖besselHalf Λ ρ hΛ hρ.le
          (iteratedFDeriv ℝ (j+1) (globalHaarColumn (some (leafPath n x))) (DyadicApproximation.realEmbed f)
            (fun i => DyadicApproximation.realEmbed (v i)))‖^2 := (mul_sum _ _ _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (hgen Λ hΛ n _ (realEmbed_real f) hf (fun i => DyadicApproximation.realEmbed (v i)) M hM hv) ha
  have hs := NegativePacketScales.coarse_mass_mesh (zero_lt_one.trans_le hΛ) hρ.le hδ
    (by positivity : 0 < (2:ℝ)^n) hc
  have hs' : T*N ≤ 4*δ^(-ρ)*L^(1-2*ρ) := by simpa only [T,hN] using hs
  have hh := mul_le_mul_of_nonneg_left hs' (by positivity : 0 ≤ HaarNegativeCoarse.constant ρ*K^2*J*E*P^2)
  exact hfinite.trans (by dsimp only [a,C,L]; nlinarith only [hh])

theorem exists_separated_middle_generation (m U : ℝ) (hm : 0 < m) (j : ℕ)
    {ρ : ℝ} (hρ : 0 < ρ) (hρhalf : ρ < 1/2) :
    ∃ C : ℝ, 0 < C ∧ ∀ (Λ δ w K : ℝ) (hΛ : 1 ≤ Λ) (hδ : 0 < δ) (hw : 0 < w),
      w ≤ 1 → δ ≤ w → 0 ≤ K → ∀ (D : HeatDominatedKernel w K hw) (n : ℕ),
      (2:ℝ)^n ≤ δ^(-(1/2:ℝ)) → ∀ (f : DyadicApproximation.RealL2),
      (∀ᵐ y ∂haarAddCircle, m ≤ (DyadicApproximation.realEmbed f y).re ∧
        (DyadicApproximation.realEmbed f y).re ≤ U) →
      ∀ (v : Fin (j+1) → DyadicApproximation.RealL2) (M : Fin (j+1) → ℝ),
      (∀ i, 0 ≤ M i) →
      (∀ i, i ≠ 0 → ∀ᵐ y ∂haarAddCircle, ‖DyadicApproximation.realEmbed (v i) y‖ ≤ M i) →
      (∑ x : Grid n,separatedJetEnergy D Λ ρ δ f j v (leafPath n x)) ≤
        C*K^2*StepInput.negativeEnergy 1 Λ ρ (DyadicApproximation.realEmbed (v 0))*
          (∏ i ∈ univ.erase (0 : Fin (j+1)), M i)^2*w^(ρ-1/2)*δ^(-ρ) := by
  obtain ⟨J,hJ,hgen⟩ := exists_globalHaarColumn_jet_negative_generation_bound m U hm j hρ hρhalf
  let R := HeatDominatedNegative.constant ρ*NegativeL1Heat.constant ρ
  have hR : 0 < R := mul_pos (HeatDominatedNegative.constant_pos hρhalf) (HaarNegativeCoarse.l1Constant_pos hρ hρhalf)
  refine ⟨2*R*J,by positivity,?_⟩
  intro Λ δ w K hΛ hδ hw hw1 hδw hK D n hn f hf v M hM hv
  let N : ℝ := ((2^(n+1):ℕ):ℝ)
  let T := min (Λ^(-ρ)*w^(-(1/2:ℝ))) (w^(ρ-1/2))*(Λ^ρ+δ^(-ρ))
  let E := StepInput.negativeEnergy 1 Λ ρ (DyadicApproximation.realEmbed (v 0))
  let P := ∏ i ∈ univ.erase (0 : Fin (j+1)), M i
  let a := R*K^2*N⁻¹*T
  have hN : 0 < N := by dsimp [N]; positivity
  have ha : 0 ≤ a := by dsimp [a,T]; positivity
  have hE : 0 ≤ E := by
    dsimp only [E]
    rw [← energy_eq_negativeEnergy Λ ρ (zero_lt_one.trans_le hΛ)]
    unfold energy
    positivity
  have hfinite : (∑ x : Grid n,separatedJetEnergy D Λ ρ δ f j v (leafPath n x)) ≤ a*(J*N*E*P^2) := by
    calc
      _ ≤ ∑ x : Grid n,a*‖besselHalf Λ ρ hΛ hρ.le
          (iteratedFDeriv ℝ (j+1) (globalHaarColumn (some (leafPath n x))) (DyadicApproximation.realEmbed f)
            (fun i => DyadicApproximation.realEmbed (v i)))‖^2 := by
        apply sum_le_sum
        intro x _
        let z := iteratedFDeriv ℝ (j+1) (globalHaarColumn (some (leafPath n x))) (DyadicApproximation.realEmbed f)
          (fun i => DyadicApproximation.realEmbed (v i))
        have hp (y : Grid ((leafPath n x).length+1)) : 0 < localAverage ((leafPath n x).length+1) (DyadicApproximation.realEmbed f) y :=
          hm.trans_le (localAverage_bounds_ae _ _ m U hf y).1
        have hL := NegativeL1Heat.supported_heat_normOne_negative hΛ hρ hρhalf hδ (leafPath n x)
          (by rw [nodeLength_leafPath]; exact coarse_generation_condition hδ n hn) z
          (globalHaarColumn_jet_supported (leafPath n x) _ hp (j+1) _)
        have ho := HeatDominatedNegative.negative_bound hΛ hρ hρhalf hw hw1 hK
          D.operator D.kernel D.measurable_kernel D.kernel_bound D.representation (heat δ z)
        have hh := ho.trans (mul_le_mul_of_nonneg_left hL (by positivity [HeatDominatedNegative.constant_pos hρhalf]))
        rw [← besselHalf_norm_sq Λ ρ hΛ hρ.le z] at hh
        rw [leafPath_length] at hh
        exact hh.trans_eq (by dsimp only [separatedJetEnergy,a,R,T,N]; ring)
      _ = a*∑ x : Grid n,‖besselHalf Λ ρ hΛ hρ.le
          (iteratedFDeriv ℝ (j+1) (globalHaarColumn (some (leafPath n x))) (DyadicApproximation.realEmbed f)
            (fun i => DyadicApproximation.realEmbed (v i)))‖^2 := (mul_sum _ _ _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (hgen Λ hΛ n _ (realEmbed_real f) hf (fun i => DyadicApproximation.realEmbed (v i)) M hM hv) ha
  have hs := SeparatedPacketScales.mass_cap (zero_lt_one.trans_le hΛ) hρ.le hδ hδw
  have hs' : T ≤ 2*w^(ρ-1/2)*δ^(-ρ) := by simpa only [T,mul_comm] using hs
  have he : a*(J*N*E*P^2) = R*K^2*J*E*P^2*T := by dsimp only [a]; field_simp
  rw [he] at hfinite
  have hh := mul_le_mul_of_nonneg_left hs' (by positivity : 0 ≤ R*K^2*J*E*P^2)
  exact hfinite.trans (by nlinarith only [hh])

theorem exists_separated_fine_generation (m U : ℝ) (hm : 0 < m) (j : ℕ)
    {ρ : ℝ} (hρ : 0 < ρ) (hρhalf : ρ < 1/2) :
    ∃ C : ℝ, 0 < C ∧ ∀ (Λ δ w K : ℝ) (hΛ : 1 ≤ Λ) (hδ : 0 < δ) (hw : 0 < w),
      w ≤ 1 → δ ≤ w → 0 ≤ K → ∀ (D : HeatDominatedKernel w K hw) (n : ℕ),
      δ^(-(1/2:ℝ)) ≤ (2:ℝ)^n → ∀ (f : DyadicApproximation.RealL2),
      (∀ᵐ y ∂haarAddCircle, m ≤ (DyadicApproximation.realEmbed f y).re ∧
        (DyadicApproximation.realEmbed f y).re ≤ U) →
      ∀ (v : Fin (j+1) → DyadicApproximation.RealL2) (M : Fin (j+1) → ℝ),
      (∀ i, 0 ≤ M i) →
      (∀ i, i ≠ 0 → ∀ᵐ y ∂haarAddCircle, ‖DyadicApproximation.realEmbed (v i) y‖ ≤ M i) →
      (∑ x : Grid n,separatedJetEnergy D Λ ρ δ f j v (leafPath n x)) ≤
        C*K^2*StepInput.negativeEnergy 1 Λ ρ (DyadicApproximation.realEmbed (v 0))*
          (∏ i ∈ univ.erase (0 : Fin (j+1)), M i)^2*w^(ρ-1/2)*δ⁻¹*((2:ℝ)^n)^(2*ρ-2) := by
  obtain ⟨J,hJ,hloc⟩ := exists_sum_localNegativeNorm_bound hρ hρhalf
  let R := HeatDominatedNegative.constant ρ*(rowPacketConstant m U hm j ρ)^2*localConstant^2
  have hR : 0 ≤ R := by dsimp [R]; positivity [HeatDominatedNegative.constant_pos hρhalf]
  let C := 1+2*R*J
  refine ⟨C,by dsimp [C]; positivity,?_⟩
  intro Λ δ w K hΛ hδ hw hw1 hδw hK D n hn f hf v M hM hv
  let L : ℝ := (2:ℝ)^n
  let N : ℝ := ((2^(n+1):ℕ):ℝ)
  let E := StepInput.negativeEnergy 1 Λ ρ (DyadicApproximation.realEmbed (v 0))
  let P := ∏ i ∈ univ.erase (0 : Fin (j+1)), M i
  let T := w^(ρ-1/2)*δ⁻¹*L^(2*ρ-2)
  have hN : N = 2*L := by dsimp [N,L]; push_cast; rw [pow_succ]; ring
  have hL : 0 < L := by dsimp [L]; positivity
  have hE : 0 ≤ E := by
    dsimp only [E]
    rw [← energy_eq_negativeEnergy Λ ρ (zero_lt_one.trans_le hΛ)]
    unfold energy
    positivity
  have hL2 : δ⁻¹ ≤ L^2 := by
    have hh := pow_le_pow_left₀ (by positivity : 0 ≤ δ^(-(1/2:ℝ))) hn 2
    rw [← Real.rpow_mul_natCast hδ.le] at hh
    norm_num only [Nat.cast_ofNat,neg_mul,one_div,inv_mul_cancel₀ (by norm_num : (2:ℝ) ≠ 0),one_mul,Real.rpow_neg_one] at hh
    exact hh
  have hNδ : δ⁻¹ ≤ N^2 := hL2.trans (by rw [hN]; nlinarith [sq_nonneg L])
  have hs := SeparatedPacketScales.fine_mass_mesh (zero_lt_one.trans_le hΛ) hρ.le (by linarith : ρ ≤ 1)
    hδ hδw (by rw [hN]; positivity) hNδ
  have hpower : N^(2*ρ-2) ≤ L^(2*ρ-2) :=
    Real.rpow_le_rpow_of_nonpos hL (by rw [hN]; linarith) (by linarith)
  have hs' : N⁻¹^2*δ⁻¹*(Λ+N^2)^ρ*min (Λ^(-ρ)*w^(-(1/2:ℝ))) (w^(ρ-1/2)) ≤ 2*T := by
    exact hs.trans (by dsimp only [T]; nlinarith [mul_le_mul_of_nonneg_left hpower (by positivity : 0 ≤ 2*δ⁻¹*w^(ρ-1/2))])
  have hfinite : (∑ x : Grid n,separatedJetEnergy D Λ ρ δ f j v (leafPath n x)) ≤
      (2*R*K^2*T*P^2)*(J*E) := by
    calc
      _ ≤ ∑ x : Grid n,(2*R*K^2*T*P^2)*
          localNegativeNorm (leafPath n x) Λ ρ hΛ hρ.le (DyadicApproximation.realEmbed (v 0))^2 := by
        apply sum_le_sum
        intro x _
        let z := iteratedFDeriv ℝ (j+1) (globalHaarColumn (some (leafPath n x))) (DyadicApproximation.realEmbed f)
          (fun i => DyadicApproximation.realEmbed (v i))
        have hL1 := globalHaarColumn_jet_fine_normOne_negative hΛ hρ hρhalf hδ (hδw.trans hw1) (leafPath n x)
          (by rw [nodeLength_leafPath]; exact fine_generation_condition hδ n hn) f m U hm hf j v M hM hv
        have ho := HeatDominatedNegative.negative_bound hΛ hρ hρhalf hw hw1 hK
          D.operator D.kernel D.measurable_kernel D.kernel_bound D.representation (heat δ z)
        have hh := ho.trans (mul_le_mul_of_nonneg_left hL1 (by positivity [HeatDominatedNegative.constant_pos hρhalf]))
        rw [leafPath_length] at hh
        have hsx := mul_le_mul_of_nonneg_left hs' (by positivity : 0 ≤ R*K^2*
          localNegativeNorm (leafPath n x) Λ ρ hΛ hρ.le (DyadicApproximation.realEmbed (v 0))^2*P^2)
        exact hh.trans (by dsimp only [separatedJetEnergy,R,N,P]; nlinarith only [hsx])
      _ = (2*R*K^2*T*P^2)*∑ x : Grid n,
          localNegativeNorm (leafPath n x) Λ ρ hΛ hρ.le (DyadicApproximation.realEmbed (v 0))^2 := (mul_sum _ _ _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left (hloc Λ hΛ n (DyadicApproximation.realEmbed (v 0))) (by dsimp [T]; positivity)
  have hc : 2*R*J ≤ C := by dsimp [C]; linarith
  have hmul := mul_le_mul_of_nonneg_right hc (by dsimp [T]; positivity : 0 ≤ K^2*E*P^2*T)
  exact hfinite.trans (by dsimp only [T,C,L]; nlinarith only [hmul])

end FiniteHaar
end SHE
