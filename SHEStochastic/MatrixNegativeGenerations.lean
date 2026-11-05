module

public import SHEStochastic.MatrixNegativeGeneration
public import SHEStochastic.MatrixFineNegative
public import SHE.HaarNegativeGenerations

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
noncomputable section

namespace SHEStochastic.MatrixNegativeGenerations
open MeasureTheory SHE SHE.FiniteHaar SHE.DyadicApproximation SHE.HaarWeightedHeat SHE.CellNegative
open MatrixInfiniteHaar MatrixPhysicalColumnSmooth MatrixActualColumnCalculus MatrixProfileEntries MatrixNegativeEntries
open scoped NNReal ENNReal MatrixOrder Matrix.Norms.L2Operator
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local notation "μ" => AddCircle.haarAddCircle (T := (1 : ℝ))
variable {d : Type*} [Fintype d] [DecidableEq d]

def packetEnergy (Λ ρ t : ℝ) (hΛ : 1 ≤ Λ) (hρ : 0 ≤ ρ) (b : CircleHeat.CircleL2) (B : ℝ)
    (hb : ∀ᵐ x ∂μ, ‖b x‖ ≤ B) (P : Profile d) (v : Domain (d := d)) (w : List (Domain (d := d))) (p : List Bool) : ℝ :=
  ∑ i : d, ∑ r : d, ‖weightedHeat Λ ρ t hΛ hρ b B hb (MatrixFinePacket.scalarColumn P p i r (v :: w))‖ ^ 2

def coarseConstant (P : Profile d) (ρ : ℝ) (hρ : 0 < ρ) (hρhalf : ρ < 1/2) (k : ℕ) : ℝ :=
  4 * HaarNegativeCoarse.constant ρ * MatrixNegativeGeneration.constant P ρ hρ hρhalf k

def fineConstant (P : Profile d) (ρ : ℝ) (hρ : 0 < ρ) (hρhalf : ρ < 1/2) (k : ℕ) : ℝ :=
  1 + 2 * (Fintype.card d : ℝ) ^ 2 * MatrixFineNegative.constant P ρ k *
    MatrixNegativeGeneration.localization (d := d) ρ hρ hρhalf

theorem coarseConstant_pos (P : Profile d) (ρ : ℝ) (hρ : 0 < ρ) (hρhalf : ρ < 1/2) (k : ℕ) :
    0 < coarseConstant P ρ hρ hρhalf k := by
  have hC := zero_lt_one.trans_le (HaarNegativeCoarse.constant_one_le ρ)
  have hK := MatrixNegativeGeneration.constant_pos P ρ hρ hρhalf k
  unfold coarseConstant
  positivity

theorem fineConstant_pos (P : Profile d) (ρ : ℝ) (hρ : 0 < ρ) (hρhalf : ρ < 1/2) (k : ℕ) :
    0 < fineConstant P ρ hρ hρhalf k := by
  have hA := MatrixFineNegative.constant_nonneg hρhalf P k
  have hL := MatrixNegativeGeneration.localization_pos (d := d) ρ hρ hρhalf
  unfold fineConstant
  positivity

theorem coarse {Λ ρ t : ℝ} (hΛ : 1 ≤ Λ) (hρ : 0 < ρ) (hρhalf : ρ < 1/2) (ht : 0 < t)
    (P : Profile d) (n : ℕ) (hn : (2 : ℝ)^n ≤ t ^ (-(1/2 : ℝ)))
    (v : Domain (d := d)) (w : List (Domain (d := d))) (M : Domain (d := d) → ℝ)
    (hM : ∀ q, 0 ≤ M q) (hRest : ∀ q ∈ w, ∀ᵐ x ∂μ, ‖q.val x‖ ≤ M q)
    (b : CircleHeat.CircleL2) (B : ℝ) (hB : 0 ≤ B) (hb : ∀ᵐ x ∂μ, ‖b x‖ ≤ B) :
    (∑ x : Grid n, packetEnergy Λ ρ t hΛ hρ.le b B hb P v w (leafPath n x)) ≤
      coarseConstant P ρ hρ hρhalf w.length * B ^ 2 * MatrixNegativeLocalization.energy Λ ρ v *
        MatrixJetClosure.weight M w ^ 2 * t ^ (-ρ) * ((2 : ℝ)^n) ^ (1-2*ρ) := by
  let D : ℝ := (2 : ℝ)^n
  let N : ℝ := ((2^(n+1):ℕ):ℝ)
  let T := (Λ^ρ+t^(-ρ))*min (Λ^(-ρ)) (N^(-2*ρ))
  let K := MatrixNegativeGeneration.constant P ρ hρ hρhalf w.length
  let E := MatrixNegativeLocalization.energy Λ ρ v
  let W := MatrixJetClosure.weight M w
  let a := HaarNegativeCoarse.constant ρ * B ^ 2 * T
  have hN : N = 2*D := by dsimp [N,D]; push_cast; rw [pow_succ]; ring
  have hC := (zero_lt_one.trans_le (HaarNegativeCoarse.constant_one_le ρ)).le
  have hK := (MatrixNegativeGeneration.constant_pos P ρ hρ hρhalf w.length).le
  have hE : 0 ≤ E := MatrixNegativeLocalization.energy_nonneg hΛ v
  have ha : 0 ≤ a := by dsimp [a,T,N]; positivity
  have hfinite : (∑ x : Grid n, packetEnergy Λ ρ t hΛ hρ.le b B hb P v w (leafPath n x)) ≤ a*(K*N*E*W^2) := by
    calc
      _ ≤ ∑ x : Grid n, ∑ i : d, ∑ r : d, a * ‖operator Λ ρ hΛ hρ.le
          (component r (MatrixPhysicalJetStructure.jetColumn P (leafPath n x) i (v :: w)))‖ ^ 2 := by
        apply Finset.sum_le_sum
        intro x hx
        apply Finset.sum_le_sum
        intro i hi
        apply Finset.sum_le_sum
        intro r hr
        have hp := HaarNegativeCoarse.packet hΛ hρ hρhalf ht (leafPath n x)
          (by rw [nodeLength_leafPath]; exact coarse_generation_condition ht n hn)
          (MatrixFinePacket.scalarColumn P (leafPath n x) i r (v :: w))
          (MatrixFinePacket.supported P (leafPath n x) i r (v :: w)) b B hB hb
        rw [← besselHalf_norm_sq (hΛ := hΛ) (hρ := hρ.le), leafPath_length] at hp
        convert! hp using 1
        dsimp only [a,T,N,operator,MatrixFinePacket.scalarColumn,ContinuousLinearMap.comp_apply]
        have he (z : CircleHeat.CircleL2) :
            ((besselHalf Λ ρ hΛ hρ.le).restrictScalars ℝ) z = besselHalf Λ ρ hΛ hρ.le z := rfl
        simp only [he]
        ring
      _ = a * ∑ x : Grid n, ∑ i : d, ∑ r : d, ‖operator Λ ρ hΛ hρ.le
          (component r (MatrixPhysicalJetStructure.jetColumn P (leafPath n x) i (v :: w)))‖ ^ 2 := by
        simp only [Finset.mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left (MatrixNegativeGeneration.bound hΛ hρ hρhalf P n v w M hM hRest) ha
  have hs := NegativePacketScales.coarse_mass_mesh (zero_lt_one.trans_le hΛ) hρ.le ht
    (by positivity : 0 < (2 : ℝ)^n) (coarse_generation_condition ht n hn)
  have hs' : T*N ≤ 4*t^(-ρ)*D^(1-2*ρ) := by simpa only [T,hN] using hs
  have hh := mul_le_mul_of_nonneg_left hs' (by positivity : 0 ≤ HaarNegativeCoarse.constant ρ*B^2*K*E*W^2)
  exact hfinite.trans (by dsimp only [a, coarseConstant, D]; nlinarith only [hh])

theorem fine {Λ ρ t : ℝ} (hΛ : 1 ≤ Λ) (hρ : 0 < ρ) (hρhalf : ρ < 1/2) (ht : 0 < t) (ht1 : t ≤ 1)
    (P : Profile d) (n : ℕ) (hn : t ^ (-(1/2 : ℝ)) ≤ (2 : ℝ)^n)
    (v : Domain (d := d)) (w : List (Domain (d := d))) (M : Domain (d := d) → ℝ)
    (hM : ∀ q, 0 ≤ M q) (hRest : ∀ q ∈ w, ∀ᵐ x ∂μ, ‖q.val x‖ ≤ M q)
    (b : CircleHeat.CircleL2) (B : ℝ) (hB : 0 ≤ B) (hb : ∀ᵐ x ∂μ, ‖b x‖ ≤ B) :
    (∑ x : Grid n, packetEnergy Λ ρ t hΛ hρ.le b B hb P v w (leafPath n x)) ≤
      fineConstant P ρ hρ hρhalf w.length * B ^ 2 * MatrixNegativeLocalization.energy Λ ρ v *
        MatrixJetClosure.weight M w ^ 2 * t ^ (ρ-3/2) * ((2 : ℝ)^n) ^ (2*ρ-2) := by
  let D : ℝ := (2 : ℝ)^n
  let N : ℝ := ((2^(n+1):ℕ):ℝ)
  let E := MatrixNegativeLocalization.energy Λ ρ v
  let W := MatrixJetClosure.weight M w
  let A := MatrixFineNegative.constant P ρ w.length
  let L := MatrixNegativeGeneration.localization (d := d) ρ hρ hρhalf
  let T := t^(ρ-3/2)*D^(2*ρ-2)
  have hN : N = 2*D := by dsimp [N,D]; push_cast; rw [pow_succ]; ring
  have hD : 0 < D := by dsimp [D]; positivity
  have hA : 0 ≤ A := MatrixFineNegative.constant_nonneg hρhalf P w.length
  have hE : 0 ≤ E := MatrixNegativeLocalization.energy_nonneg hΛ v
  have hD2 : t⁻¹ ≤ D^2 := by
    have hh := pow_le_pow_left₀ (by positivity : 0 ≤ t^(-(1/2 : ℝ))) hn 2
    rw [← Real.rpow_mul_natCast ht.le] at hh
    norm_num only [Nat.cast_ofNat, neg_mul, one_div, inv_mul_cancel₀ (by norm_num : (2 : ℝ) ≠ 0), one_mul, Real.rpow_neg_one] at hh
    exact hh
  have hNt : t⁻¹ ≤ N^2 := hD2.trans (by rw [hN]; nlinarith [sq_nonneg D])
  have hs := NegativePacketScales.fine_mass_mesh (zero_lt_one.trans_le hΛ) hρ.le (by linarith : ρ ≤ 1)
    ht (by rw [hN]; positivity) hNt
  have hpower : N^(2*ρ-2) ≤ D^(2*ρ-2) := Real.rpow_le_rpow_of_nonpos hD (by rw [hN]; linarith) (by linarith)
  have hs' : N⁻¹^2*t⁻¹*(Λ+N^2)^ρ*min (Λ^(-ρ)*t^(-(1/2 : ℝ))) (t^(ρ-1/2)) ≤ 2*T :=
    hs.trans (by dsimp only [T]; nlinarith [mul_le_mul_of_nonneg_left hpower (by positivity : 0 ≤ 2*t^(ρ-3/2))])
  have hfinite : (∑ x : Grid n, packetEnergy Λ ρ t hΛ hρ.le b B hb P v w (leafPath n x)) ≤
      (2*(Fintype.card d : ℝ)^2*A*B^2*T*W^2)*(L*E) := by
    calc
      _ ≤ ∑ x : Grid n, ∑ i : d, ∑ r : d, (2*A*B^2*T*W^2)*localNorm (leafPath n x) Λ ρ hΛ hρ.le v ^ 2 := by
        apply Finset.sum_le_sum
        intro x hx
        apply Finset.sum_le_sum
        intro i hi
        apply Finset.sum_le_sum
        intro r hr
        have hh := MatrixFineNegative.bound hΛ hρ hρhalf ht ht1 P (leafPath n x)
          (by rw [nodeLength_leafPath]; exact fine_generation_condition ht n hn) i r v w M hM hRest b B hB hb
        rw [leafPath_length] at hh
        have hm := mul_le_mul_of_nonneg_left hs' (by positivity : 0 ≤ A*B^2*localNorm (leafPath n x) Λ ρ hΛ hρ.le v ^ 2*W^2)
        exact hh.trans (by dsimp only [A,N,W]; nlinarith only [hm])
      _ = (2*(Fintype.card d : ℝ)^2*A*B^2*T*W^2)*∑ x : Grid n, localNorm (leafPath n x) Λ ρ hΛ hρ.le v ^ 2 := by
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro x hx
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left
        ((MatrixNegativeLocalization.exists_generation (d := d) hρ hρhalf).choose_spec.2 Λ hΛ n v)
        (by dsimp [T]; positivity)
  have hc : 2*(Fintype.card d : ℝ)^2*A*L ≤ fineConstant P ρ hρ hρhalf w.length := by unfold fineConstant; dsimp [A,L]; linarith
  have hm := mul_le_mul_of_nonneg_right hc (by dsimp [T]; positivity : 0 ≤ B^2*E*W^2*T)
  exact hfinite.trans (by dsimp only [T,D]; nlinarith only [hm])

end SHEStochastic.MatrixNegativeGenerations
