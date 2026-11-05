module

public import SHE.CircleL1Dual
public import SHE.BoundedHeat

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1800000
noncomputable section

namespace SHE.NegativeL1Heat
open Finset Set MeasureTheory AddCircle CircleHeat CircleFractional FiniteHaar CellTranslation SmoothCellSobolev
  CoarseCellSobolev CircleL1Dual ArcFourier ArcNegative HaarWeightedHeat HeatMarkov
open scoped ENNReal InnerProductSpace
local instance negativeL1Heat_periodPos : Fact (0 < (1:ℝ)) := ⟨zero_lt_one⟩

def constant (ρ : ℝ) : ℝ := 4*coarseConstant ρ (localConstant+2)

/-- Actual localized L¹ smoothing of a negative Sobolev input. The
proof tests against the literal complex sign of the heated output,
uses the genuine bounded heat representative, and applies the proved
coarse-cell positive Sobolev estimate. No shell/smoothing premise is
assumed. -/
theorem supported_heat_normOne_negative {Λ ρ t : ℝ} (hΛ : 1 ≤ Λ)
    (hρ : 0 < ρ) (hρhalf : ρ < 1/2) (ht : 0 < t) (p : List Bool)
    (hcoarse : Real.sqrt t ≤ nodeLength p) (v : CircleL2)
    (hv : ∀ᵐ y ∂haarAddCircle, y ∉ nodeCell p → v y = 0) :
    normOne (heat t v)^2 ≤ constant ρ*(((2^(p.length+1):ℕ):ℝ))⁻¹*(Λ^ρ+t^(-ρ))*NegativeNash.energy Λ ρ v := by
  let σ := sign (heat t v)
  have hσ : ∀ᵐ y ∂haarAddCircle, ‖σ y‖ ≤ 1 := sign_bound (heat t v)
  let u := BoundedHeat.representative ht σ 1 zero_le_one hσ
  let w := heat t σ
  have he : ContinuousMap.toLp 2 haarAddCircle ℂ u = w := by
    apply Lp.ext
    exact (ContinuousMap.coeFn_toLp haarAddCircle u).trans (BoundedHeat.representative_ae ht σ 1 zero_le_one hσ)
  have hΛ0 : 0 < Λ := zero_lt_one.trans_le hΛ
  have hchild (b : Bool) := coarse_cut_massive hΛ hρ hρhalf ht (p.length+1) (bottomLeaf p b)
    hcoarse u (localConstant+2) (by positivity [localConstant_pos])
    (fun y _ => BoundedHeat.norm_bound ht σ hσ y)
    (fun y _ z _ => by
      have hh := BoundedHeat.difference_bound ht σ zero_le_one hσ y z
      simpa only [u,BoundedHeat.representative,ContinuousMap.coe_mk,BoundedHeat.lipConstant,mul_one] using! hh)
  have hcell (b : Bool) : cellRestriction (p.length+1) (bottomLeaf p b) w =
      CellRow.cutLp (p.length+1) (bottomLeaf p b) u := by
    rw [CellRow.cutLp_eq_restriction,he]
  have hc (b : Bool) := fourierCoeff_congr_ae (CellRow.cutLp_ae (p.length+1) (bottomLeaf p b) u)
  have hsum (b : Bool) : Summable (fun k : ℤ => weight Λ ρ k*
      ‖fourierCoeff (cellRestriction (p.length+1) (bottomLeaf p b) w) k‖^2) := by
    simpa only [hcell b,hc b] using! (hchild b).1
  have hpos (b : Bool) : positiveSq Λ ρ (cellRestriction (p.length+1) (bottomLeaf p b) w) ≤
      coarseConstant ρ (localConstant+2)*(((2^(p.length+1):ℕ):ℝ))⁻¹*(Λ^ρ+t^(-ρ)) := by
    simpa only [positiveSq,hcell b,hc b] using! (hchild b).2
  have ha := massive_add_bound hΛ0.le _ _ (hsum false) (hsum true)
  let g := nodeRestriction p w
  have hg : Summable (fun k : ℤ => weight Λ ρ k*‖fourierBasis.repr g k‖^2) := by
    simpa only [fourierBasis_repr] using! ha.1
  have hb : InputProjection.weightedEnergy fourierBasis (weight Λ ρ) g ≤
      constant ρ*(((2^(p.length+1):ℕ):ℝ))⁻¹*(Λ^ρ+t^(-ρ)) := by
    have hh := ha.2.trans (mul_le_mul_of_nonneg_left (add_le_add (hpos false) (hpos true)) (by norm_num : (0:ℝ) ≤ 2))
    change positiveSq Λ ρ g ≤ _ at hh
    have hh' : positiveSq Λ ρ g ≤ constant ρ*(((2^(p.length+1):ℕ):ℝ))⁻¹*(Λ^ρ+t^(-ρ)) :=
      hh.trans_eq (by unfold constant; ring)
    simpa only [InputProjection.weightedEnergy,fourierBasis_repr,positiveSq] using! hh'
  have hp : ‖inner ℂ v g‖ = normOne (heat t v) := by
    rw [norm_inner_symm]
    change ‖inner ℂ (nodeRestriction p w) v‖ = _
    rw [← nodeRestriction_inner,nodeRestriction_eq_of_supported p v hv]
    change ‖inner ℂ (heat t σ) v‖ = _
    rw [heat_inner,sign_pair,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (normOne_nonneg _)]
  have hcs := InputProjection.weighted_cauchy fourierBasis (weight Λ ρ)
    (fun k => Real.rpow_pos_of_pos (by positivity : 0 < Λ+(k:ℝ)^2) _) v g
    (by simpa only [fourierBasis_repr] using negative_summable hΛ0 hρ.le v) hg
  rw [hp] at hcs
  have hE : InputProjection.weightedEnergy fourierBasis (fun k => (weight Λ ρ k)⁻¹) v = NegativeNash.energy Λ ρ v := by
    simp only [InputProjection.weightedEnergy,fourierBasis_repr,weight,NegativeNash.energy]
    apply tsum_congr
    intro k
    rw [Real.rpow_neg (by positivity : 0 ≤ Λ+(k:ℝ)^2)]
  rw [hE] at hcs
  have hEn : 0 ≤ NegativeNash.energy Λ ρ v := by unfold NegativeNash.energy; positivity
  exact (hcs.trans (mul_le_mul_of_nonneg_left hb hEn)).trans_eq (by ring)

end SHE.NegativeL1Heat
