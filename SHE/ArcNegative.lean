module

public import SHE.ArcFourier

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1800000
noncomputable section

namespace SHE.ArcNegative
open Finset Set MeasureTheory AddCircle CircleHeat ArcGeometry ArcSobolev ArcFourier
open scoped ENNReal InnerProductSpace
local instance arcNegative_periodPos : Fact (0 < (1:ℝ)) := ⟨zero_lt_one⟩

def restriction (a b : ℝ) (f : CircleL2) : CircleL2 :=
  ((Lp.memLp f).indicator (measurableSet_arcSet a b).nullMeasurableSet).toLp _

theorem restriction_ae (a b : ℝ) (f : CircleL2) :
    restriction a b f =ᵐ[haarAddCircle] (arcSet a b).indicator f :=
  ((Lp.memLp f).indicator (measurableSet_arcSet a b).nullMeasurableSet).coeFn_toLp

theorem restriction_inner (a b : ℝ) (f g : CircleL2) :
    inner ℂ f (restriction a b g) = inner ℂ (restriction a b f) g := by
  rw [L2.inner_def,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [restriction_ae a b f,restriction_ae a b g] with x hf hg
  rw [hf,hg]
  by_cases hx : x ∈ arcSet a b
  · simp only [Set.indicator_of_mem hx]
  · simp only [Set.indicator_of_notMem hx,inner_zero_left,inner_zero_right]

def polynomial (F : Finset ℤ) (v : ℤ → ℂ) : C(AddCircle (1:ℝ),ℂ) :=
  ∑ n ∈ F, v n • fourier n

theorem polynomial_coeff (F : Finset ℤ) (v : ℤ → ℂ) (k : ℤ) :
    fourierCoeff (polynomial F v) k = if k ∈ F then v k else 0 := by
  classical
  have hf (n : ℤ) : Integrable (v n • (fourier n : AddCircle (1:ℝ) → ℂ)) haarAddCircle :=
    (((fourier n).memLp haarAddCircle ℂ).integrable (by norm_num : (1:ℝ≥0∞) ≤ 1)).smul _
  have he := congrFun (fourierCoeff.sum F (fun n => v n • (fourier n : AddCircle (1:ℝ) → ℂ)) (fun n _ => hf n)) k
  convert he.trans ?_ using 1
  · simp only [polynomial,ContinuousMap.coe_sum,ContinuousMap.coe_smul]
  simp only [Finset.sum_apply,fourierCoeff.const_smul,fourierCoeff_fourier,Pi.single_apply,
    smul_eq_mul,mul_ite,mul_one,mul_zero]
  simp only [Finset.sum_ite_eq]

theorem polynomial_summable (Λ ρ : ℝ) (F : Finset ℤ) (v : ℤ → ℂ) :
    Summable (fun n : ℤ => weight Λ ρ n*‖fourierCoeff (polynomial F v) n‖^2) := by
  classical
  apply summable_of_ne_finset_zero (s := F)
  intro n hn
  simp only [polynomial_coeff,ite_eq_right hn,norm_zero,zero_pow (by norm_num : (2:ℕ) ≠ 0),mul_zero]

theorem polynomial_energy (Λ ρ : ℝ) (F : Finset ℤ) (v : ℤ → ℂ) :
    positiveSq Λ ρ (polynomial F v) = ∑ n ∈ F, weight Λ ρ n*‖v n‖^2 := by
  classical
  unfold positiveSq
  rw [tsum_eq_sum (s := F) (fun n hn => by simp [polynomial_coeff,hn])]
  apply Finset.sum_congr rfl
  intro n hn
  rw [polynomial_coeff,ite_eq_left hn]

def negativeSq (Λ ρ : ℝ) (f : CircleL2) : ℝ :=
  ∑' n : ℤ, (weight Λ ρ n)⁻¹*‖fourierCoeff f n‖^2

theorem negative_summable {Λ ρ : ℝ} (hΛ : 0 < Λ) (hρ : 0 ≤ ρ) (f : CircleL2) :
    Summable (fun n : ℤ => (weight Λ ρ n)⁻¹*‖fourierCoeff f n‖^2) := by
  have he (n : ℤ) : (weight Λ ρ n)⁻¹ = (Λ+(n:ℝ)^2)^(-ρ) := by
    rw [weight,Real.rpow_neg (by positivity : 0 ≤ Λ+(n:ℝ)^2)]
  simpa only [he] using NegativeNash.energy_summable hΛ hρ f

theorem negative_nonneg {Λ ρ : ℝ} (hΛ : 0 ≤ Λ) (f : CircleL2) : 0 ≤ negativeSq Λ ρ f :=
  tsum_nonneg (fun _n => mul_nonneg (inv_nonneg.mpr (Real.rpow_nonneg (add_nonneg hΛ (sq_nonneg _)) _)) (sq_nonneg _))

theorem restriction_polynomial_ae (a b : ℝ) (F : Finset ℤ) (v : ℤ → ℂ) :
    restriction a b (ContinuousMap.toLp 2 haarAddCircle ℂ (polynomial F v)) =ᵐ[haarAddCircle]
      cutoff a b (polynomial F v) := by
  have hpoly : (ContinuousMap.toLp 2 haarAddCircle ℂ (polynomial F v)) =ᵐ[haarAddCircle] polynomial F v :=
    ContinuousMap.coeFn_toLp haarAddCircle (polynomial F v)
  filter_upwards [restriction_ae a b (ContinuousMap.toLp 2 haarAddCircle ℂ (polynomial F v)),hpoly] with x hr hp
  rw [hr]
  by_cases hx : x ∈ arcSet a b
  · simp only [cutoff,Set.indicator_of_mem hx,hp]
  · simp only [cutoff,Set.indicator_of_notMem hx]

theorem polynomial_pair (F : Finset ℤ) (v : CircleL2) (Λ ρ : ℝ) :
    inner ℂ v (ContinuousMap.toLp 2 haarAddCircle ℂ
      (polynomial F (fun n => ((weight Λ ρ n)⁻¹ : ℂ)*fourierCoeff v n))) =
      ((∑ n ∈ F, (weight Λ ρ n)⁻¹*‖fourierCoeff v n‖^2 : ℝ) : ℂ) := by
  classical
  rw [← fourierBasis.repr.inner_map_map,lp.inner_eq_tsum]
  simp_rw [fourierBasis_repr,fourierCoeff_toLp,polynomial_coeff]
  rw [tsum_eq_sum (s := F) (fun n hn => by simp only [ite_eq_right hn,inner_zero_right])]
  rw [Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro n hn
  rw [ite_eq_left hn]
  change inner ℂ (fourierCoeff v n) (((weight Λ ρ n)⁻¹ : ℂ) • fourierCoeff v n) = _
  rw [inner_smul_right,inner_self_eq_norm_sq_to_K,Complex.ofReal_mul]
  push_cast
  rfl

theorem dual_polynomial_energy {Λ : ℝ} (hΛ : 0 < Λ) (ρ : ℝ) (F : Finset ℤ) (v : CircleL2) :
    positiveSq Λ ρ (polynomial F (fun n => ((weight Λ ρ n)⁻¹ : ℂ)*fourierCoeff v n)) =
      ∑ n ∈ F, (weight Λ ρ n)⁻¹*‖fourierCoeff v n‖^2 := by
  rw [polynomial_energy]
  apply Finset.sum_congr rfl
  intro n _
  have hw : 0 < weight Λ ρ n := Real.rpow_pos_of_pos (by positivity) _
  rw [norm_mul,mul_pow,norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hw]
  field_simp

/-- Literal interval restriction is uniformly bounded in the actual
negative massive Fourier norm, for arbitrary complex L² inputs.
The duality proof uses actual finite Fourier polynomials. -/
theorem exists_negative_restriction_bound {ρ : ℝ} (hρ : 0 < ρ) (hρhalf : ρ < 1/2) :
    ∃ C : ℝ, 0 < C ∧ ∀ (Λ : ℝ), 1 ≤ Λ → ∀ (a b : ℝ) (f : CircleL2),
      negativeSq Λ ρ (restriction a b f) ≤ C*negativeSq Λ ρ f := by
  obtain ⟨C,hC,hbound⟩ := exists_massive_cutoff_bound hρ hρhalf
  refine ⟨C,hC,?_⟩
  intro Λ hΛ a b f
  have hΛ0 : 0 < Λ := zero_lt_one.trans_le hΛ
  let v := restriction a b f
  have hpartial (F : Finset ℤ) : (∑ n ∈ F, (weight Λ ρ n)⁻¹*‖fourierCoeff v n‖^2) ≤ C*negativeSq Λ ρ f := by
    let u := polynomial F (fun n => ((weight Λ ρ n)⁻¹ : ℂ)*fourierCoeff v n)
    let g : CircleL2 := ContinuousMap.toLp 2 haarAddCircle ℂ u
    let E := ∑ n ∈ F, (weight Λ ρ n)⁻¹*‖fourierCoeff v n‖^2
    have hE : 0 ≤ E := Finset.sum_nonneg (fun n _ => by unfold weight; positivity)
    have huc := hbound Λ hΛ a b u (polynomial_summable Λ ρ F _)
    have hcoef : fourierCoeff (restriction a b g) = fourierCoeff (cutoff a b u) := by
      simpa only [u,g] using! fourierCoeff_congr_ae (restriction_polynomial_ae a b F (fun n => ((weight Λ ρ n)⁻¹ : ℂ)*fourierCoeff v n))
    have hgs : Summable (fun n : ℤ => weight Λ ρ n*‖fourierBasis.repr (restriction a b g) n‖^2) := by
      simpa only [fourierBasis_repr,hcoef] using! huc.1
    have hcs := InputProjection.weighted_cauchy fourierBasis (weight Λ ρ)
      (fun n => Real.rpow_pos_of_pos (by positivity : 0 < Λ+(n:ℝ)^2) _) f (restriction a b g)
      (by simpa only [fourierBasis_repr] using negative_summable hΛ0 hρ.le f) hgs
    have hpair : inner ℂ f (restriction a b g) = (E : ℂ) := by
      rw [restriction_inner]
      exact polynomial_pair F v Λ ρ
    have hpositive : InputProjection.weightedEnergy fourierBasis (weight Λ ρ) (restriction a b g) ≤ C*E := by
      have hh := huc.2
      rw [dual_polynomial_energy hΛ0 ρ F v] at hh
      simpa only [InputProjection.weightedEnergy,fourierBasis_repr,hcoef,positiveSq] using! hh
    rw [hpair,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hE] at hcs
    have hcs' : E^2 ≤ negativeSq Λ ρ f*InputProjection.weightedEnergy fourierBasis (weight Λ ρ) (restriction a b g) := by
      simpa only [InputProjection.weightedEnergy,fourierBasis_repr,negativeSq] using! hcs
    have hmul := mul_le_mul_of_nonneg_left hpositive (negative_nonneg (ρ := ρ) hΛ0.le f)
    change E ≤ C*negativeSq Λ ρ f
    by_cases hz : E = 0
    · rw [hz]
      exact mul_nonneg hC.le (negative_nonneg (ρ := ρ) hΛ0.le f)
    · have hEp : 0 < E := lt_of_le_of_ne hE (Ne.symm hz)
      have hh : E*E ≤ (C*negativeSq Λ ρ f)*E := by nlinarith only [hcs',hmul]
      exact (mul_le_mul_iff_left₀ hEp).mp hh
  exact Real.tsum_le_of_sum_le (fun n => by unfold weight; positivity) hpartial

end SHE.ArcNegative
