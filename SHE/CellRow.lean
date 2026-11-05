module

public import SHE.SmoothCellSobolev

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section

namespace SHE.CellRow
open Finset Set MeasureTheory AddCircle CircleHeat CircleFractional FiniteHaar CellTranslation SmoothCellSobolev
  HaarWeightedHeat ArcFourier ArcNegative CellNegative
open scoped ENNReal InnerProductSpace
local instance cellRow_periodPos : Fact (0 < (1:ℝ)) := ⟨zero_lt_one⟩

def row (u : C(AddCircle (1:ℝ),ℂ)) : CircleL2 →L[ℂ] ℂ :=
  innerSL ℂ (ContinuousMap.toLp 2 haarAddCircle ℂ u)

def cutLp (n : ℕ) (x : Grid n) (u : C(AddCircle (1:ℝ),ℂ)) : CircleL2 := (cut_memLp n x u).toLp _

theorem cutLp_ae (n : ℕ) (x : Grid n) (u : C(AddCircle (1:ℝ),ℂ)) :
    cutLp n x u =ᵐ[haarAddCircle] cut n x u := (cut_memLp n x u).coeFn_toLp

theorem cutLp_eq_restriction (n : ℕ) (x : Grid n) (u : C(AddCircle (1:ℝ),ℂ)) :
    cutLp n x u = cellRestriction n x (ContinuousMap.toLp 2 haarAddCircle ℂ u) := by
  have hto : (ContinuousMap.toLp 2 haarAddCircle ℂ u) =ᵐ[haarAddCircle] u := ContinuousMap.coeFn_toLp haarAddCircle u
  apply Lp.ext
  filter_upwards [cutLp_ae n x u,cellRestriction_ae n x (ContinuousMap.toLp 2 haarAddCircle ℂ u),hto] with y hc hr hu
  rw [hc,hr]
  by_cases hy : y ∈ cellSet n x
  · simp only [cut,Set.indicator_of_mem hy,hu]
  · simp only [cut,Set.indicator_of_notMem hy]

theorem row_cell_norm (n : ℕ) (x : Grid n) (u : C(AddCircle (1:ℝ),ℂ)) (v : CircleL2) :
    ‖row u (cellRestriction n x v)‖ = ‖inner ℂ (cellRestriction n x v) (cutLp n x u)‖ := by
  rw [norm_inner_symm,cutLp_eq_restriction,← cellRestriction_inner,cellRestriction_idempotent]
  rfl

theorem cutLp_norm_sq (n : ℕ) (x : Grid n) (u : C(AddCircle (1:ℝ),ℂ)) :
    ‖cutLp n x u‖^2 = ∫ y, ‖cut n x u y‖^2 ∂haarAddCircle := by
  rw [StoppedFourier.L2_norm_sq_eq_integral]
  exact integral_congr_ae ((cutLp_ae n x u).fun_comp (fun z : ℂ => ‖z‖^2))

theorem row_bounded {n : ℕ} (x : Grid n) (u : C(AddCircle (1:ℝ),ℂ)) (L : ℝ) (hL : 0 ≤ L)
    (hu : ∀ y ∈ cellSet n x, ‖u y‖ ≤ 2*L/(((2^n:ℕ):ℝ)))
    (v : CircleL2) (M : ℝ) (hM : 0 ≤ M) (hv : ∀ᵐ y ∂haarAddCircle, ‖v y‖ ≤ M) :
    ‖row u (cellRestriction n x v)‖ ≤ 2*L*M/(((2^n:ℕ):ℝ))^2 := by
  let N : ℝ := ((2^n:ℕ):ℝ)
  have hN : 0 < N := by dsimp [N]; positivity
  have hs : (Real.sqrt N)^2 = N := Real.sq_sqrt hN.le
  have hinv : (Real.sqrt N)⁻¹^2 = N⁻¹ := by rw [inv_pow,hs]
  have hcut : ‖cutLp n x u‖ ≤ 2*L*(Real.sqrt N)⁻¹^3 := by
    apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
    rw [cutLp_norm_sq]
    have hb := cut_square_bound n x u (2*L/N) hu
    apply hb.trans_eq
    have hpow : ((Real.sqrt N)⁻¹^3)^2 = N⁻¹^3 := by
      rw [← pow_mul,show (3:ℕ)*2 = 2*3 by omega,pow_mul,hinv]
    rw [mul_pow,mul_pow,hpow]
    dsimp only [N] at *
    field_simp
  rw [row_cell_norm]
  have hb := (norm_inner_le_norm (𝕜 := ℂ) (cellRestriction n x v) (cutLp n x u)).trans
    (mul_le_mul (cellRestriction_bounded_norm n x v M hM hv) hcut (norm_nonneg _) (by positivity))
  apply hb.trans_eq
  dsimp only [N] at *
  have hfour : (Real.sqrt (((2^n:ℕ):ℝ)))^4 = (((2^n:ℕ):ℝ))^2 := by nlinarith [congrArg (fun r : ℝ => r^2) hs]
  field_simp
  rw [hfour]
  ring

theorem row_negative {Λ ρ : ℝ} (hΛ : 1 ≤ Λ) (hρ : 0 < ρ) (hρhalf : ρ < 1/2)
    (n : ℕ) (x : Grid n) (u : C(AddCircle (1:ℝ),ℂ)) (L : ℝ) (hL : 0 ≤ L)
    (hu : ∀ y ∈ cellSet n x, ‖u y‖ ≤ 2*L/(((2^n:ℕ):ℝ)))
    (hlip : ∀ y ∈ cellSet n x, ∀ w ∈ cellSet n x, ‖u y-u w‖ ≤ L*dist y w)
    (v : CircleL2) :
    ‖row u (cellRestriction n x v)‖ ≤ Real.sqrt (SmoothCellSobolev.packetConstant ρ)*L*
      (Real.sqrt (((2^n:ℕ):ℝ)))⁻¹^3*scale Λ ρ n*
        ‖besselHalf Λ ρ hΛ hρ.le (cellRestriction n x v)‖ := by
  let N : ℝ := ((2^n:ℕ):ℝ)
  have hN : 0 < N := by dsimp [N]; positivity
  have hΛ0 : 0 < Λ := zero_lt_one.trans_le hΛ
  have hK := (SmoothCellSobolev.packetConstant_pos hρ hρhalf).le
  let v' := cellRestriction n x v
  have hs := small_amplitude_massive_bound hΛ hρ hρhalf n x u L hL hu hlip
  have he := fourierCoeff_congr_ae (cutLp_ae n x u)
  have hp : InputProjection.weightedEnergy fourierBasis (weight Λ ρ) (cutLp n x u) = positiveSq Λ ρ (cut n x u) := by
    simp only [InputProjection.weightedEnergy,fourierBasis_repr,he,positiveSq]
  have hn : InputProjection.weightedEnergy fourierBasis (fun k => (weight Λ ρ k)⁻¹) v' = NegativeNash.energy Λ ρ v' := by
    simp only [InputProjection.weightedEnergy,fourierBasis_repr,weight,NegativeNash.energy]
    apply tsum_congr
    intro k
    rw [Real.rpow_neg (by positivity : 0 ≤ Λ+(k:ℝ)^2)]
  have hc := InputProjection.weighted_cauchy fourierBasis (weight Λ ρ)
    (fun k => Real.rpow_pos_of_pos (by positivity : 0 < Λ+(k:ℝ)^2) _) v' (cutLp n x u)
    (by simpa only [fourierBasis_repr] using negative_summable hΛ0 hρ.le v')
    (by simpa only [fourierBasis_repr,he] using! hs.1)
  rw [hp,hn] at hc
  have hEn : 0 ≤ NegativeNash.energy Λ ρ v' := by unfold NegativeNash.energy; positivity
  have hb := hc.trans (mul_le_mul_of_nonneg_left hs.2 hEn)
  rw [row_cell_norm]
  apply (sq_le_sq₀ (norm_nonneg _) (by unfold scale; positivity)).mp
  apply hb.trans_eq
  rw [mul_pow,mul_pow,mul_pow,mul_pow,Real.sq_sqrt hK,besselHalf_norm_sq]
  have hsqrt := Real.sq_sqrt hN.le
  have hscale : scale Λ ρ n^2 = (Λ+N^2)^ρ := by
    dsimp only [N]
    rw [scale,← Real.rpow_mul_natCast (by positivity : 0 ≤ Λ+(((2^n:ℕ):ℝ))^2)]
    norm_num
  have hinv : (Real.sqrt (((2^n:ℕ):ℝ)))⁻¹^2 = (((2^n:ℕ):ℝ))⁻¹ := by
    rw [inv_pow,Real.sq_sqrt (by positivity)]
  rw [hscale,← pow_mul,show (3:ℕ)*2 = 2*3 by omega,pow_mul,hinv]
  dsimp only [N,v']
  ring

end SHE.CellRow
