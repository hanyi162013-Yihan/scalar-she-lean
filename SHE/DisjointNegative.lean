module

public import SHE.DisjointArcs

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1800000
noncomputable section

namespace SHE.DisjointNegative
open Finset Set MeasureTheory AddCircle CircleHeat ArcGeometry ArcSobolev ArcFourier ArcNegative DisjointArcs
open scoped ENNReal InnerProductSpace
local instance disjointNegative_periodPos : Fact (0 < (1:ℝ)) := ⟨zero_lt_one⟩

variable {I : Type*} [Fintype I]

def assemblyLp (a b : I → ℝ) (u : I → C(AddCircle (1:ℝ),ℂ)) : CircleL2 :=
  ∑ i, restriction (a i) (b i) (ContinuousMap.toLp 2 haarAddCircle ℂ (u i))

theorem assemblyLp_ae (a b : I → ℝ) (u : I → C(AddCircle (1:ℝ),ℂ)) :
    assemblyLp a b u =ᵐ[haarAddCircle] assembly a b u := by
  have hpoly : ∀ i, (ContinuousMap.toLp 2 haarAddCircle ℂ (u i)) =ᵐ[haarAddCircle] u i :=
    fun i => ContinuousMap.coeFn_toLp haarAddCircle (u i)
  filter_upwards [Lp.coeFn_fun_finsetSum Finset.univ (fun i => restriction (a i) (b i) (ContinuousMap.toLp 2 haarAddCircle ℂ (u i))),
    ae_all_iff.mpr (fun i => restriction_ae (a i) (b i) (ContinuousMap.toLp 2 haarAddCircle ℂ (u i))),
    ae_all_iff.mpr hpoly] with x hs hr hp
  rw [show assemblyLp a b u x = _ from hs]
  apply Finset.sum_congr rfl
  intro i _
  rw [hr i]
  by_cases hx : x ∈ arcSet (a i) (b i)
  · simp only [cutoff,Set.indicator_of_mem hx,hp i]
  · simp only [cutoff,Set.indicator_of_notMem hx]

/-- Actual negative massive Fourier energy localizes over every finite
disjoint family of literal circle intervals. The single constant is
uniform in Λ ≥ 1, the number of cells, and all interval lengths. -/
theorem exists_negative_localization_bound {ρ : ℝ} (hρ : 0 < ρ) (hρhalf : ρ < 1/2) :
    ∃ C : ℝ, 0 < C ∧ ∀ (J : Type) [Fintype J] (Λ : ℝ), 1 ≤ Λ →
      ∀ (a b : J → ℝ),
      (∀ i j, i ≠ j → Disjoint (arcSet (a i) (b i)) (arcSet (a j) (b j))) →
      ∀ f : CircleL2, (∑ i, negativeSq Λ ρ (restriction (a i) (b i) f)) ≤ C*negativeSq Λ ρ f := by
  classical
  obtain ⟨C,hC,hbound⟩ := exists_massive_assembly_bound hρ hρhalf
  refine ⟨C,hC,?_⟩
  intro J _ Λ hΛ a b hd f
  have hΛ0 : 0 < Λ := zero_lt_one.trans_le hΛ
  let v : J → CircleL2 := fun i => restriction (a i) (b i) f
  have hpartial (F : Finset ℤ) :
      (∑ i, ∑ n ∈ F, (weight Λ ρ n)⁻¹*‖fourierCoeff (v i) n‖^2) ≤ C*negativeSq Λ ρ f := by
    let u : J → C(AddCircle (1:ℝ),ℂ) := fun i =>
      polynomial F (fun n => ((weight Λ ρ n)⁻¹ : ℂ)*fourierCoeff (v i) n)
    let g : CircleL2 := assemblyLp a b u
    let E : ℝ := ∑ i, ∑ n ∈ F, (weight Λ ρ n)⁻¹*‖fourierCoeff (v i) n‖^2
    have hE : 0 ≤ E := Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun n _ => by unfold weight; positivity))
    have hu := hbound J Λ hΛ a b u hd (fun i => polynomial_summable Λ ρ F _)
    have hcoef : fourierCoeff g = fourierCoeff (assembly a b u) := fourierCoeff_congr_ae (assemblyLp_ae a b u)
    have hgs : Summable (fun n : ℤ => weight Λ ρ n*‖fourierBasis.repr g n‖^2) := by
      simpa only [fourierBasis_repr,hcoef] using! hu.1
    have hcs := InputProjection.weighted_cauchy fourierBasis (weight Λ ρ)
      (fun n => Real.rpow_pos_of_pos (by positivity : 0 < Λ+(n:ℝ)^2) _) f g
      (by simpa only [fourierBasis_repr] using negative_summable hΛ0 hρ.le f) hgs
    have hpair : inner ℂ f g = (E : ℂ) := by
      change inner ℂ f (∑ i, restriction (a i) (b i) (ContinuousMap.toLp 2 haarAddCircle ℂ (u i))) = _
      rw [inner_sum,Complex.ofReal_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [restriction_inner]
      exact polynomial_pair F (v i) Λ ρ
    have hpositive : InputProjection.weightedEnergy fourierBasis (weight Λ ρ) g ≤ C*E := by
      have hh := hu.2
      have he (i : J) : positiveSq Λ ρ (u i) = ∑ n ∈ F, (weight Λ ρ n)⁻¹*‖fourierCoeff (v i) n‖^2 :=
        dual_polynomial_energy hΛ0 ρ F (v i)
      simp only [he] at hh
      simpa only [InputProjection.weightedEnergy,fourierBasis_repr,hcoef,positiveSq,E] using! hh
    rw [hpair,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hE] at hcs
    have hcs' : E^2 ≤ negativeSq Λ ρ f*InputProjection.weightedEnergy fourierBasis (weight Λ ρ) g := by
      simpa only [InputProjection.weightedEnergy,fourierBasis_repr,negativeSq] using! hcs
    have hmul := mul_le_mul_of_nonneg_left hpositive (negative_nonneg (ρ := ρ) hΛ0.le f)
    change E ≤ C*negativeSq Λ ρ f
    by_cases hz : E = 0
    · rw [hz]
      exact mul_nonneg hC.le (negative_nonneg (ρ := ρ) hΛ0.le f)
    · have hEp : 0 < E := lt_of_le_of_ne hE (Ne.symm hz)
      have hh : E*E ≤ (C*negativeSq Λ ρ f)*E := by nlinarith only [hcs',hmul]
      exact (mul_le_mul_iff_left₀ hEp).mp hh
  have he : (∑ i, negativeSq Λ ρ (v i)) =
      ∑' n : ℤ, ∑ i, (weight Λ ρ n)⁻¹*‖fourierCoeff (v i) n‖^2 := by
    exact (Summable.tsum_finsetSum (fun i _ => negative_summable hΛ0 hρ.le (v i))).symm
  rw [show (∑ i, negativeSq Λ ρ (restriction (a i) (b i) f)) = _ from he]
  apply Real.tsum_le_of_sum_le (fun n => Finset.sum_nonneg (fun i _ => by unfold weight; positivity))
  intro F
  rw [Finset.sum_comm]
  exact hpartial F

end SHE.DisjointNegative
