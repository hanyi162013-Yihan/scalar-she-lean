module

public import SHE.ArcNegative
public import Mathlib.Algebra.Order.Chebyshev

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1800000
noncomputable section

namespace SHE.DisjointArcs
open Finset Set MeasureTheory AddCircle CircleHeat CircleFractional FractionalHardy ArcGeometry ArcSobolev ArcFourier ArcNegative
open scoped ENNReal
local instance disjointArcs_periodPos : Fact (0 < (1:ℝ)) := ⟨zero_lt_one⟩

variable {I : Type*} [Fintype I]

theorem sparse_sum_sq_le (d : I → ℂ) (S : Finset I) (k : ℕ) (hcard : S.card ≤ k)
    (hzero : ∀ i ∉ S, d i = 0) : ‖∑ i, d i‖^2 ≤ (k:ℝ)*∑ i, ‖d i‖^2 := by
  classical
  have he : ∑ i, d i = ∑ i ∈ S, d i := (Finset.sum_subset (Finset.subset_univ S) (fun i _ hi => hzero i hi)).symm
  rw [he]
  calc
    _ ≤ (∑ i ∈ S, ‖d i‖)^2 := pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le S d) 2
    _ ≤ (S.card:ℝ)*∑ i ∈ S, ‖d i‖^2 := sq_sum_le_card_mul_sum_sq
    _ ≤ (k:ℝ)*∑ i, ‖d i‖^2 := mul_le_mul
      (by exact_mod_cast hcard) (Finset.sum_le_univ_sum_of_nonneg (fun _ => sq_nonneg _))
      (Finset.sum_nonneg (fun _ _ => sq_nonneg _)) (by positivity)

theorem membership_card_le_one (S : I → Set (AddCircle (1:ℝ)))
    (hS : ∀ i j, i ≠ j → Disjoint (S i) (S j)) (x : AddCircle (1:ℝ)) [DecidablePred (fun i => x ∈ S i)] :
    ((Finset.univ : Finset I).filter (fun i => x ∈ S i)).card ≤ 1 := by
  classical
  apply Finset.card_le_one.mpr
  intro i hi j hj
  by_contra hne
  exact (Set.disjoint_left.mp (hS i j hne)) (Finset.mem_filter.mp hi).2 (Finset.mem_filter.mp hj).2

theorem indicator_sum_square (S : I → Set (AddCircle (1:ℝ)))
    (hS : ∀ i j, i ≠ j → Disjoint (S i) (S j)) (u : I → AddCircle (1:ℝ) → ℂ)
    (x : AddCircle (1:ℝ)) :
    ‖∑ i, (S i).indicator (u i) x‖^2 ≤ ∑ i, ‖u i x‖^2 := by
  classical
  have hh := sparse_sum_sq_le (fun i => (S i).indicator (u i) x)
    (Finset.univ.filter (fun i => x ∈ S i)) 1 (membership_card_le_one S hS x) (by
      intro i hi
      have hx : x ∉ S i := by simpa only [Finset.mem_filter,Finset.mem_univ,true_and] using hi
      exact Set.indicator_of_notMem hx _)
  norm_num only [Nat.cast_one,one_mul] at hh
  exact hh.trans (Finset.sum_le_sum (fun i _ => by
    by_cases hx : x ∈ S i
    · rw [Set.indicator_of_mem hx]
    · rw [Set.indicator_of_notMem hx,norm_zero,zero_pow (by norm_num : (2:ℕ) ≠ 0)]
      exact sq_nonneg _))

theorem indicator_sum_difference_square (S : I → Set (AddCircle (1:ℝ)))
    (hS : ∀ i j, i ≠ j → Disjoint (S i) (S j)) (u : I → AddCircle (1:ℝ) → ℂ)
    (x y : AddCircle (1:ℝ)) :
    ‖(∑ i, (S i).indicator (u i) y)-(∑ i, (S i).indicator (u i) x)‖^2 ≤
      2*∑ i, ‖(S i).indicator (u i) y-(S i).indicator (u i) x‖^2 := by
  classical
  let A := Finset.univ.filter (fun i => x ∈ S i)
  let B := Finset.univ.filter (fun i => y ∈ S i)
  have hcard : (A ∪ B).card ≤ 2 := (Finset.card_union_le A B).trans (by
    have ha := membership_card_le_one S hS x
    have hb := membership_card_le_one S hS y
    dsimp only [A,B]
    omega)
  have hh := sparse_sum_sq_le (fun i => (S i).indicator (u i) y-(S i).indicator (u i) x)
    (A∪B) 2 hcard (by
      intro i hi
      have hx : x ∉ S i := by
        intro hx
        exact hi (Finset.mem_union.mpr (Or.inl (Finset.mem_filter.mpr ⟨Finset.mem_univ i,hx⟩)))
      have hy : y ∉ S i := by
        intro hy
        exact hi (Finset.mem_union.mpr (Or.inr (Finset.mem_filter.mpr ⟨Finset.mem_univ i,hy⟩)))
      rw [Set.indicator_of_notMem hx,Set.indicator_of_notMem hy,sub_self])
  simpa only [Finset.sum_sub_distrib,Nat.cast_ofNat] using hh

def assembly (a b : I → ℝ) (u : I → C(AddCircle (1:ℝ),ℂ)) (x : AddCircle (1:ℝ)) : ℂ :=
  ∑ i, cutoff (a i) (b i) (u i) x

theorem assembly_measurable (a b : I → ℝ) (u : I → C(AddCircle (1:ℝ),ℂ)) :
    Measurable (assembly a b u) := by
  exact Finset.measurable_sum _ (fun i _ => cutoff_measurable (a i) (b i) (u i))

theorem assembly_memLp (a b : I → ℝ) (u : I → C(AddCircle (1:ℝ),ℂ)) :
    MemLp (assembly a b u) 2 haarAddCircle := by
  exact memLp_finsetSum Finset.univ (f := fun i x => cutoff (a i) (b i) (u i) x)
    (fun i _ => cutoff_memLp (a i) (b i) (u i))

theorem assembly_square_le (a b : I → ℝ) (u : I → C(AddCircle (1:ℝ),ℂ))
    (hd : ∀ i j, i ≠ j → Disjoint (arcSet (a i) (b i)) (arcSet (a j) (b j))) :
    (∫ x, ‖assembly a b u x‖^2 ∂haarAddCircle) ≤ ∑ i, circleSquare (u i) := by
  have hs (i : I) : Integrable (fun x => ‖u i x‖^2) haarAddCircle :=
    (memLp_two_iff_integrable_sq_norm ((u i).memLp (p := 2) haarAddCircle ℂ).aestronglyMeasurable).mp ((u i).memLp haarAddCircle ℂ)
  unfold circleSquare
  rw [← integral_finsetSum Finset.univ (fun i _ => hs i)]
  apply integral_mono ((memLp_two_iff_integrable_sq_norm (assembly_memLp a b u).aestronglyMeasurable).mp (assembly_memLp a b u))
    (integrable_finsetSum _ (fun i _ => hs i))
  intro x
  exact indicator_sum_square (fun i => arcSet (a i) (b i)) hd (fun i => u i) x

theorem assembly_product_integrable {ρ : ℝ} (hρ : 0 < ρ) (hρhalf : ρ < 1/2)
    (a b : I → ℝ) (u : I → C(AddCircle (1:ℝ),ℂ))
    (hd : ∀ i j, i ≠ j → Disjoint (arcSet (a i) (b i)) (arcSet (a j) (b j)))
    (hG : ∀ i, IntegrableOn (fun z : ℝ => circleTranslationEnergy (u i) z*z^(-1-2*ρ)) (Ioi 0)) :
    Integrable (fun p : ℝ × AddCircle (1:ℝ) => ‖assembly a b u (p.2+(p.1 : AddCircle (1:ℝ)))-assembly a b u p.2‖^2*p.1^(-1-2*ρ))
      ((volume.restrict (Ioi 0)).prod haarAddCircle) := by
  have hsum := integrable_finsetSum Finset.univ (fun i _ => cutoff_product_integrable hρ hρhalf (a i) (b i) (u i) (hG i))
  have hm : Measurable (fun p : ℝ × AddCircle (1:ℝ) => ‖assembly a b u (p.2+(p.1 : AddCircle (1:ℝ)))-assembly a b u p.2‖^2*p.1^(-1-2*ρ)) := by
    exact (((assembly_measurable a b u).comp (by fun_prop)).sub ((assembly_measurable a b u).comp measurable_snd)).norm.pow_const 2 |>.mul (by fun_prop)
  apply (hsum.const_mul 2).mono' hm.aestronglyMeasurable
  filter_upwards [positive_prod] with p hp
  rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hp.le _))]
  have hh := mul_le_mul_of_nonneg_right
    (indicator_sum_difference_square (fun i => arcSet (a i) (b i)) hd (fun i => u i) p.2 (p.2+(p.1 : AddCircle (1:ℝ))))
    (Real.rpow_nonneg hp.le (-1-2*ρ))
  simpa only [assembly,cutoff,Finset.sum_mul,mul_assoc] using hh

theorem assembly_gagliardo_bound {ρ : ℝ} (hρ : 0 < ρ) (hρhalf : ρ < 1/2)
    (a b : I → ℝ) (u : I → C(AddCircle (1:ℝ),ℂ))
    (hd : ∀ i j, i ≠ j → Disjoint (arcSet (a i) (b i)) (arcSet (a j) (b j)))
    (hG : ∀ i, IntegrableOn (fun z : ℝ => circleTranslationEnergy (u i) z*z^(-1-2*ρ)) (Ioi 0)) :
    IntegrableOn (fun z : ℝ => circleTranslationEnergy (assembly a b u) z*z^(-1-2*ρ)) (Ioi 0) ∧
      circleFractionalSq ρ (assembly a b u) ≤ 2*∑ i, circleFractionalSq ρ (cutoff (a i) (b i) (u i)) := by
  have hi := assembly_product_integrable hρ hρhalf a b u hd hG
  refine ⟨?_,?_⟩
  · simpa only [circleTranslationEnergy,integral_mul_const] using! hi.integral_prod_left
  let F : I → ℝ × AddCircle (1:ℝ) → ℝ := fun i p =>
    ‖cutoff (a i) (b i) (u i) (p.2+(p.1 : AddCircle (1:ℝ)))-cutoff (a i) (b i) (u i) p.2‖^2*p.1^(-1-2*ρ)
  have hF (i : I) : Integrable (F i) ((volume.restrict (Ioi 0)).prod haarAddCircle) :=
    cutoff_product_integrable hρ hρhalf (a i) (b i) (u i) (hG i)
  have hmajor := (integrable_finsetSum Finset.univ (fun i _ => hF i)).const_mul 2
  have hb := integral_mono_ae hi hmajor (by
    filter_upwards [positive_prod] with p hp
    have hh := mul_le_mul_of_nonneg_right
      (indicator_sum_difference_square (fun i => arcSet (a i) (b i)) hd (fun i => u i) p.2 (p.2+(p.1 : AddCircle (1:ℝ))))
      (Real.rpow_nonneg hp.le (-1-2*ρ))
    simpa only [F,assembly,cutoff,Finset.sum_mul,mul_assoc] using hh)
  rw [integral_const_mul,integral_finsetSum Finset.univ (fun i _ => hF i),integral_prod _ hi] at hb
  have he (i : I) : (∫ p, F i p ∂(volume.restrict (Ioi 0)).prod haarAddCircle) = circleFractionalSq ρ (cutoff (a i) (b i) (u i)) := by
    rw [integral_prod _ (hF i)]
    simp only [F,integral_mul_const,circleFractionalSq,circleTranslationEnergy]
  simp only [he,integral_mul_const] at hb
  simpa only [circleFractionalSq,circleTranslationEnergy] using! hb

/-- Disjoint interval assembly is bounded in the actual positive
massive Fourier norm, with a constant independent of the number and
lengths of the intervals. -/
theorem exists_massive_assembly_bound {ρ : ℝ} (hρ : 0 < ρ) (hρhalf : ρ < 1/2) :
    ∃ C : ℝ, 0 < C ∧ ∀ (J : Type) [Fintype J] (Λ : ℝ), 1 ≤ Λ → ∀ (a b : J → ℝ)
      (u : J → C(AddCircle (1:ℝ),ℂ)),
      (∀ i j, i ≠ j → Disjoint (arcSet (a i) (b i)) (arcSet (a j) (b j))) →
      (∀ i, Summable (fun n : ℤ => weight Λ ρ n*‖fourierCoeff (u i) n‖^2)) →
      Summable (fun n : ℤ => weight Λ ρ n*‖fourierCoeff (assembly a b u) n‖^2) ∧
        positiveSq Λ ρ (assembly a b u) ≤ C*∑ i, positiveSq Λ ρ (u i) := by
  classical
  obtain ⟨C,hC,hcut⟩ := exists_cutoff_gagliardo_bound hρ hρhalf
  let M := unitFractionalMass ρ
  have hM : 0 < M := unitFractionalMass_pos hρ hρhalf
  refine ⟨1+2*M⁻¹*C*(1+M),by positivity,?_⟩
  intro J _ Λ hΛ a b u hd hs
  have hΛ0 := zero_le_one.trans hΛ
  have hmass : 1 ≤ Λ^ρ := Real.one_le_rpow hΛ hρ.le
  have hu (i : J) := continuous_gagliardo_of_massive hΛ0 hρ hρhalf (u i) (hs i)
  have hass := assembly_gagliardo_bound hρ hρhalf a b u hd (fun i => (hu i).1)
  refine ⟨massive_summable_of_gagliardo hΛ0 hρ hρhalf _ (assembly_memLp a b u) hass.1,?_⟩
  have hb := massive_le_base_gagliardo hΛ0 hρ hρhalf _ (assembly_memLp a b u) hass.1
  have hbase := mul_le_mul_of_nonneg_left (assembly_square_le a b u hd) (Real.rpow_nonneg hΛ0 ρ)
  have hsumBase : Λ^ρ*(∑ i, circleSquare (u i)) ≤ ∑ i, positiveSq Λ ρ (u i) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun i _ => massive_base_le hΛ0 hρ.le (u i) (hs i))
  have hcuti (i : J) : circleFractionalSq ρ (cutoff (a i) (b i) (u i)) ≤
      C*(1+M)*positiveSq Λ ρ (u i) := by
    have hh := hcut (a i) (b i) (u i) (hu i).1
    have hbi := massive_base_le hΛ0 hρ.le (u i) (hs i)
    have hsq0 := circleSquare_nonneg (u i)
    have hsq : circleSquare (u i) ≤ positiveSq Λ ρ (u i) := by nlinarith
    have hgi : circleFractionalSq ρ (u i) ≤ M*positiveSq Λ ρ (u i) := (hu i).2
    nlinarith
  have hsumG := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hcuti i)
  rw [← Finset.mul_sum] at hsumG
  have hscale := mul_le_mul_of_nonneg_left hass.2 (inv_nonneg.mpr hM.le)
  have hscale2 := mul_le_mul_of_nonneg_left hsumG (by positivity : 0 ≤ 2*M⁻¹)
  change positiveSq Λ ρ (assembly a b u) ≤ Λ^ρ*(∫ x, ‖assembly a b u x‖^2 ∂haarAddCircle)+M⁻¹*circleFractionalSq ρ (assembly a b u) at hb
  nlinarith

end SHE.DisjointArcs
