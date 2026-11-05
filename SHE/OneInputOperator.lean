module

public import SHE.HistoryFrames
public import SHE.SquareSummableColumns

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace SHE.OneInputOperator
open MeasureTheory AddCircle StoppedFourier
open scoped ENNReal
local instance : Fact (0 < 2*Real.pi) := ⟨by positivity⟩

theorem modulation_memLp (d : CircleL2) (l : ℤ) :
    MemLp (fun x : HeatCircle => fourier l x*d x) 2 haarAddCircle := by
  apply (Lp.memLp d).of_le ((fourier l).continuous.aestronglyMeasurable.mul (Lp.aestronglyMeasurable d))
  filter_upwards with x
  simp [fourier_apply]

/-- Multiplication by an actual unit-modulus circle Fourier mode. -/
def modulate (l : ℤ) (d : CircleL2) : CircleL2 :=
  (modulation_memLp d l).toLp (fun x : HeatCircle => fourier l x*d x)

theorem modulate_fourierCoeff (l k : ℤ) (d : CircleL2) :
    fourierCoeff (modulate l d) k = fourierCoeff d (k-l) := by
  rw [modulate,fourierCoeff_congr_ae (modulation_memLp d l).coeFn_toLp]
  simp only [fourierCoeff,smul_eq_mul]
  apply integral_congr_ae
  filter_upwards with x
  rw [← mul_assoc,← fourier_add]
  rw [show -k+l = -(k-l) by ring]

theorem massive_multiplier_le_one {Λ ρ : ℝ} (hΛ : 1 ≤ Λ) (hρ : 0 ≤ ρ) (k : ℤ) :
    ‖(((Λ+(k:ℝ)^2)^(-ρ/2):ℝ):ℂ)‖ ≤ 1 := by
  rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (Real.rpow_nonneg (by positivity) _)]
  exact Real.rpow_le_one_of_one_le_of_nonpos (by nlinarith [sq_nonneg (k:ℝ)]) (by linarith)

/-- The actual massive Bessel square root on circle L². -/
def besselHalf (Λ ρ : ℝ) (hΛ : 1 ≤ Λ) (hρ : 0 ≤ ρ) : CircleL2 →L[ℂ] CircleL2 :=
  (fourierBasis (T:=2*Real.pi)).repr.symm.toLinearIsometry.toContinuousLinearMap.comp
    ((fourierDiagonal (fun k => (((Λ+(k:ℝ)^2)^(-ρ/2):ℝ):ℂ))
      (massive_multiplier_le_one hΛ hρ)).comp
        (fourierBasis (T:=2*Real.pi)).repr.toLinearIsometry.toContinuousLinearMap)

theorem besselHalf_fourierCoeff (Λ ρ : ℝ) (hΛ : 1 ≤ Λ) (hρ : 0 ≤ ρ)
    (d : CircleL2) (k : ℤ) :
    fourierCoeff (besselHalf Λ ρ hΛ hρ d) k =
      (((Λ+(k:ℝ)^2)^(-ρ/2):ℝ):ℂ)*fourierCoeff d k := by
  rw [← fourierBasis_repr]
  change ((fourierBasis (T:=2*Real.pi)).repr
    ((fourierBasis (T:=2*Real.pi)).repr.symm _)) k = _
  rw [LinearIsometryEquiv.apply_symm_apply]
  change (((Λ+(k:ℝ)^2)^(-ρ/2):ℝ):ℂ)*(fourierBasis (T:=2*Real.pi)).repr d k = _
  rw [fourierBasis_repr]

theorem besselHalf_norm_le (Λ ρ : ℝ) (hΛ : 1 ≤ Λ) (hρ : 0 ≤ ρ) (d : CircleL2) :
    ‖besselHalf Λ ρ hΛ hρ d‖ ≤ ‖d‖ := by
  change ‖(fourierBasis (T:=2*Real.pi)).repr.symm
    ((fourierDiagonal (fun k => (((Λ+(k:ℝ)^2)^(-ρ/2):ℝ):ℂ))
      (massive_multiplier_le_one hΛ hρ)) ((fourierBasis (T:=2*Real.pi)).repr d))‖ ≤ ‖d‖
  rw [LinearIsometryEquiv.norm_map]
  exact (fourierDiagonalLinearMap_norm_le _ (massive_multiplier_le_one hΛ hρ) _).trans_eq
    (LinearIsometryEquiv.norm_map _ _)

theorem besselHalf_opNorm_le (Λ ρ : ℝ) (hΛ : 1 ≤ Λ) (hρ : 0 ≤ ρ) :
    ‖besselHalf Λ ρ hΛ hρ‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num : (0:ℝ)≤1)
  intro d
  simpa only [one_mul] using besselHalf_norm_le Λ ρ hΛ hρ d

/-- A literal Fourier column of Q^(1/2) S_t M_d S_s. The potentially
unbounded L² multiplier acts on a bounded Fourier mode, so the column
is defined without assuming an L² multiplication operator. -/
def column (Λ ρ t s : ℝ) (hΛ : 1 ≤ Λ) (hρ : 0 ≤ ρ) (ht : 0 ≤ t)
    (d : CircleL2) (l : ℤ) : CircleL2 :=
  (Real.exp (-s*(l:ℝ)^2):ℂ) •
    besselHalf Λ ρ hΛ hρ (circleHeatOperator t ht (modulate l d))

theorem column_fourierCoeff (Λ ρ t s : ℝ) (hΛ : 1 ≤ Λ) (hρ : 0 ≤ ρ) (ht : 0 ≤ t)
    (d : CircleL2) (l k : ℤ) :
    fourierCoeff (column Λ ρ t s hΛ hρ ht d l) k =
      (Real.exp (-s*(l:ℝ)^2):ℂ)*(((Λ+(k:ℝ)^2)^(-ρ/2):ℝ):ℂ)*
        (Real.exp (-t*(k:ℝ)^2):ℂ)*fourierCoeff d (k-l) := by
  rw [column,fourierCoeff_congr_ae (Lp.coeFn_smul _ _),fourierCoeff.const_smul,
    besselHalf_fourierCoeff,circleHeatOperator_fourierCoeff,modulate_fourierCoeff]
  simp only [smul_eq_mul]
  ring

theorem column_fourierCoeff_norm_sq (Λ ρ t s : ℝ)
    (hΛ : 1 ≤ Λ) (hρ : 0 ≤ ρ) (ht : 0 ≤ t) (d : CircleL2) (l k : ℤ) :
    ‖fourierCoeff (column Λ ρ t s hΛ hρ ht d l) k‖^2 =
      HeatTrace.matrixEnergy Λ ρ (2*t) (2*s) (fourierCoeff d) (k,l) := by
  have hb : 0 ≤ Λ+(k:ℝ)^2 := by positivity
  have hw : 0 ≤ (Λ+(k:ℝ)^2)^(-ρ/2) := Real.rpow_nonneg hb _
  rw [column_fourierCoeff]
  simp only [norm_mul,mul_pow,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg hw,abs_of_pos (Real.exp_pos _)]
  rw [← Real.rpow_mul_natCast hb]
  norm_num only [Nat.cast_ofNat]
  rw [show (-ρ/2)*(2:ℝ) = -ρ by ring]
  have he (u v : ℝ) : Real.exp (-u*v^2)^2 = Real.exp (-(2*u)*v^2) := by
    rw [pow_two,← Real.exp_add]
    congr 1
    ring
  rw [he,he]
  unfold HeatTrace.matrixEnergy
  simp only [sub_eq_add_neg,Real.exp_add,neg_mul]
  ring

theorem norm_sq_fourier (f : CircleL2) : ‖f‖^2=∑' k : ℤ, ‖fourierCoeff f k‖^2 := by
  rw [← fourierBasis.repr.norm_map f]
  have hh := lp.norm_rpow_eq_tsum (by norm_num : 0<(2:ENNReal).toReal) (fourierBasis.repr f)
  simpa only [ENNReal.toReal_ofNat,Real.rpow_two,fourierBasis_repr] using hh

theorem summable_fourier_sq (f : CircleL2) : Summable (fun k : ℤ => ‖fourierCoeff f k‖^2) := by
  simpa only [ENNReal.toReal_ofNat,Real.rpow_two,fourierBasis_repr] using
    (lp.memℓp (fourierBasis.repr f)).summable (by norm_num)

/-- Physical one-input trace estimate: the actual Fourier columns
have square-summable L² norms and obey the asserted heat-tree power.
Both heat ages remain present, and the input is an arbitrary L² field. -/
theorem one_input_trace {Λ ρ t s : ℝ}
    (hΛ : 1 ≤ Λ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ<1/2)
    (ht : 0 ≤ t) (hs : 0 ≤ s) (hage : 0<t+s) (hsmall : t+s≤1)
    (d : CircleL2) :
    Summable (fun l : ℤ => ‖column Λ ρ t s hΛ hρ0 ht d l‖^2) ∧
      (∑' l : ℤ, ‖column Λ ρ t s hΛ hρ0 ht d l‖^2) ≤
        ((1+2*HeatTrace.fractionalGaussianIntegral ρ)*(t+s)^(ρ-1/2))*‖d‖^2 := by
  have hh := HeatTrace.one_weight_matrix_energy hΛ hρ0 hρ1 ht hs hage hsmall
    (fourierCoeff d) (summable_fourier_sq d)
  have hcmp (kl : ℤ × ℤ) :
      HeatTrace.matrixEnergy Λ ρ (2*t) (2*s) (fourierCoeff d) kl ≤
        HeatTrace.matrixEnergy Λ ρ t s (fourierCoeff d) kl := by
    unfold HeatTrace.matrixEnergy
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply Real.exp_le_exp.mpr
    nlinarith [mul_nonneg ht (sq_nonneg (kl.1:ℝ)),mul_nonneg hs (sq_nonneg (kl.2:ℝ))]
  have hactual : Summable (HeatTrace.matrixEnergy Λ ρ (2*t) (2*s) (fourierCoeff d)) :=
    Summable.of_nonneg_of_le (fun kl => by unfold HeatTrace.matrixEnergy; positivity) hcmp hh.1
  have hcol (l : ℤ) : ‖column Λ ρ t s hΛ hρ0 ht d l‖^2 =
      ∑' k : ℤ, HeatTrace.matrixEnergy Λ ρ (2*t) (2*s) (fourierCoeff d) (k,l) := by
    rw [norm_sq_fourier]
    apply tsum_congr
    intro k
    exact column_fourierCoeff_norm_sq Λ ρ t s hΛ hρ0 ht d l k
  have houter : Summable (fun l : ℤ => ∑' k : ℤ,
      HeatTrace.matrixEnergy Λ ρ (2*t) (2*s) (fourierCoeff d) (k,l)) := hactual.prod_symm.prod
  refine ⟨by simpa only [hcol] using houter, ?_⟩
  calc
    _ = ∑' l : ℤ, ∑' k : ℤ, HeatTrace.matrixEnergy Λ ρ (2*t) (2*s) (fourierCoeff d) (k,l) := by
      simp only [hcol]
    _ = ∑' lk : ℤ × ℤ, HeatTrace.matrixEnergy Λ ρ (2*t) (2*s) (fourierCoeff d) (lk.2,lk.1) :=
      hactual.prod_symm.tsum_prod.symm
    _ = ∑' kl, HeatTrace.matrixEnergy Λ ρ (2*t) (2*s) (fourierCoeff d) kl :=
      (Equiv.prodComm ℤ ℤ).tsum_eq _
    _ ≤ ∑' kl, HeatTrace.matrixEnergy Λ ρ t s (fourierCoeff d) kl :=
      hactual.tsum_le_tsum hcmp hh.1
    _ ≤ _ := by simpa only [← norm_sq_fourier] using hh.2

/-- The physical column family defines a genuine bounded operator on
the full circle L² space. On every Fourier polynomial it is exactly
Q^(1/2) S_t M_d S_s, by the checked action on each basis vector. -/
def operator (Λ ρ t s : ℝ) (hΛ : 1 ≤ Λ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ<1/2)
    (ht : 0 ≤ t) (hs : 0 ≤ s) (hage : 0<t+s) (hsmall : t+s≤1)
    (d : CircleL2) : CircleL2 →L[ℂ] CircleL2 :=
  (SquareSummableColumns.operator (column Λ ρ t s hΛ hρ0 ht d)
    (one_input_trace hΛ hρ0 hρ1 ht hs hage hsmall d).1).comp
      (fourierBasis (T:=2*Real.pi)).repr.toLinearIsometry.toContinuousLinearMap

theorem operator_basis (Λ ρ t s : ℝ) (hΛ : 1 ≤ Λ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ<1/2)
    (ht : 0 ≤ t) (hs : 0 ≤ s) (hage : 0<t+s) (hsmall : t+s≤1)
    (d : CircleL2) (l : ℤ) :
    operator Λ ρ t s hΛ hρ0 hρ1 ht hs hage hsmall d (fourierBasis (T:=2*Real.pi) l) =
      column Λ ρ t s hΛ hρ0 ht d l := by
  change SquareSummableColumns.operator (column Λ ρ t s hΛ hρ0 ht d)
    (one_input_trace hΛ hρ0 hρ1 ht hs hage hsmall d).1
      ((fourierBasis (T:=2*Real.pi)).repr ((fourierBasis (T:=2*Real.pi)) l)) = _
  rw [HilbertBasis.repr_self,SquareSummableColumns.operator_single]

/-- The actual bounded operator has the physical one-weight heat
Hilbert--Schmidt estimate, expressed as a full orthonormal-basis square
sum. This is a conclusion about genuine operators, not a matrix bound
postulated for an unspecified physical object. -/
theorem operator_trace_bound {Λ ρ t s : ℝ}
    (hΛ : 1 ≤ Λ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ<1/2)
    (ht : 0 ≤ t) (hs : 0 ≤ s) (hage : 0<t+s) (hsmall : t+s≤1)
    (d : CircleL2) :
    (∑' l : ℤ, ‖operator Λ ρ t s hΛ hρ0 hρ1 ht hs hage hsmall d
      (fourierBasis (T:=2*Real.pi) l)‖^2) ≤
        ((1+2*HeatTrace.fractionalGaussianIntegral ρ)*(t+s)^(ρ-1/2))*‖d‖^2 := by
  simp only [operator_basis]
  exact (one_input_trace hΛ hρ0 hρ1 ht hs hage hsmall d).2

end SHE.OneInputOperator
