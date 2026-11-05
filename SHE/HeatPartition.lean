module

public import SHE.HeatCoherence
public import SHE.HeatCluster
public import SHE.SeparatedSums

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace SHE.HeatPartition
open Finset SimpleGraph MeasureTheory HeatCoherence HeatLine

variable {I : Type*} [Fintype I]

instance componentFintype (G : SimpleGraph I) : Fintype G.ConnectedComponent := Fintype.ofFinite _

def vertices (G : SimpleGraph I) (C : G.ConnectedComponent) : Finset I := by
  classical
  exact univ.filter (fun i => G.connectedComponentMk i = C)

@[simp] theorem mem_vertices (G : SimpleGraph I) (C : G.ConnectedComponent) (i : I) :
    i ∈ vertices G C ↔ G.connectedComponentMk i = C := by
  classical
  simp [vertices]

theorem vertices_nonempty (G : SimpleGraph I) (C : G.ConnectedComponent) :
    (vertices G C).Nonempty := by
  obtain ⟨i,hi⟩ := C.exists_rep
  exact ⟨i,(mem_vertices G C i).mpr hi⟩

theorem sum_components {E : Type*} [AddCommMonoid E] (G : SimpleGraph I) (f : I → E) :
    (∑ C : G.ConnectedComponent, ∑ i ∈ vertices G C,f i) = ∑ i,f i := by
  classical
  simp only [vertices,sum_filter]
  rw [sum_comm]
  simp

theorem card_components_le (G : SimpleGraph I) : Fintype.card G.ConnectedComponent ≤ Fintype.card I :=
  Fintype.card_le_of_surjective G.connectedComponentMk (fun C => C.exists_rep)

theorem exists_representative (G : SimpleGraph I) (t : I → ℝ) (C : G.ConnectedComponent) :
    ∃ r ∈ vertices G C, ∀ i ∈ vertices G C,t i ≤ t r :=
  Finset.exists_max_image _ t (vertices_nonempty G C)

def representative (G : SimpleGraph I) (t : I → ℝ) (C : G.ConnectedComponent) : I :=
  Classical.choose (exists_representative G t C)

theorem representative_mem (G : SimpleGraph I) (t : I → ℝ) (C : G.ConnectedComponent) :
    representative G t C ∈ vertices G C := (Classical.choose_spec (exists_representative G t C)).1

@[simp] theorem representative_component (G : SimpleGraph I) (t : I → ℝ) (C : G.ConnectedComponent) :
    G.connectedComponentMk (representative G t C) = C :=
  (mem_vertices G C _).mp (representative_mem G t C)

theorem age_le_representative (G : SimpleGraph I) (t : I → ℝ) (C : G.ConnectedComponent)
    {i : I} (hi : i ∈ vertices G C) : t i ≤ t (representative G t C) :=
  (Classical.choose_spec (exists_representative G t C)).2 i hi

theorem representative_injective (G : SimpleGraph I) (t : I → ℝ) :
    Function.Injective (representative G t) := by
  intro C D hCD
  have hh := congrArg G.connectedComponentMk hCD
  simpa only [representative_component] using hh

theorem sum_representatives_le (G : SimpleGraph I) (t w : I → ℝ) (hw : ∀ i,0 ≤ w i) :
    (∑ C : G.ConnectedComponent,w (representative G t C)) ≤ ∑ i,w i := by
  classical
  calc
    _ = ∑ i ∈ univ.image (representative G t),w i := by
      rw [sum_image]
      exact fun C _ D _ h => representative_injective G t h
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun i _ _ => hw i)

def paddedAge (G : SimpleGraph I) (t : I → ℝ) (C : G.ConnectedComponent) (i : I) : ℝ := by
  classical
  exact if i ∈ vertices G C then t i else t (representative G t C)

def paddedCenter (G : SimpleGraph I) (t a : I → ℝ) (C : G.ConnectedComponent) (i : I) : ℝ := by
  classical
  exact if i ∈ vertices G C then a i else a (representative G t C)

def clusterFunction (G : SimpleGraph I) (t a : I → ℝ) (z : I → ℂ) (C : G.ConnectedComponent) : ℂ → ℂ :=
  ∑ i ∈ vertices G C,z i • heatEntire (t i) (a i)

theorem clusterFunction_padded_span (G : SimpleGraph I) (t a : I → ℝ) (z : I → ℂ)
    (C : G.ConnectedComponent) :
    clusterFunction G t a z C ∈ Submodule.span ℂ (Set.range
      (fun i => heatEntire (paddedAge G t C i) (paddedCenter G t a C i))) := by
  classical
  apply (Submodule.mem_span_range_iff_exists_fun ℂ).mpr
  refine ⟨fun i => if i ∈ vertices G C then z i else 0,?_⟩
  unfold clusterFunction
  simp only [ite_smul,zero_smul]
  rw [← sum_filter]
  have he : univ.filter (fun i => i ∈ vertices G C) = vertices G C := by ext i; simp
  rw [he]
  apply sum_congr rfl
  intro i hi
  simp [hi,paddedAge,paddedCenter]

theorem clusterFunction_sum (G : SimpleGraph I) (t a : I → ℝ) (z : I → ℂ) :
    (∑ C : G.ConnectedComponent,clusterFunction G t a z C) =
      ∑ i,z i • heatEntire (t i) (a i) := sum_components G _

theorem reachable_of_mem (G : SimpleGraph I) (C : G.ConnectedComponent) {i j : I}
    (hi : i ∈ vertices G C) (hj : j ∈ vertices G C) : G.Reachable i j := by
  apply ConnectedComponent.exact
  rw [(mem_vertices G C i).mp hi,(mem_vertices G C j).mp hj]

/-- Zero-padding a real component to the original observation count
gives genuine compact-cluster parameters, even when its rank drops. -/
theorem padded_geometry (t a : I → ℝ) (ht : ∀ i,0 < t i) {K : ℝ} (hK : 1 ≤ K)
    (C : (graph t a K).ConnectedComponent) (i : I) :
    (K^(Fintype.card I))⁻¹*t (representative (graph t a K) t C) ≤ paddedAge (graph t a K) t C i ∧
      paddedAge (graph t a K) t C i ≤ t (representative (graph t a K) t C) ∧
      |paddedCenter (graph t a K) t a C i-a (representative (graph t a K) t C)| ≤
        (Fintype.card I:ℝ)*K*Real.sqrt (t (representative (graph t a K) t C)) := by
  classical
  let G := graph t a K
  let r := representative G t C
  have hK0 : 0 < K := zero_lt_one.trans_le hK
  have hp : 0 < K^(Fintype.card I) := pow_pos hK0 _
  have hdiv {s : ℝ} (hs : t r ≤ K^(Fintype.card I)*s) :
      (K^(Fintype.card I))⁻¹*t r ≤ s := by
    rw [inv_mul_eq_div]
    exact (div_le_iff₀ hp).mpr (by simpa only [mul_comm] using hs)
  by_cases hi : i ∈ vertices G C
  · have hri : G.Reachable r i := reachable_of_mem G C (representative_mem G t C) hi
    have hage := reachable_age_bound t a (fun j => (ht j).le) hK hri
    have hcenter := reachable_center_bound t a hK0.le hri (fun v hrv =>
      age_le_representative G t C ((mem_vertices G C v).mpr
        ((ConnectedComponent.sound hrv).symm.trans (representative_component G t C))))
    have hi0 : i ∈ vertices (graph t a K) C := hi
    simp only [paddedAge,paddedCenter,hi0,ite_true]
    exact ⟨hdiv hage,age_le_representative G t C hi,by rw [abs_sub_comm]; exact hcenter⟩
  · have hpow : 1 ≤ K^(Fintype.card I) := one_le_pow₀ hK
    have hself : t r ≤ K^(Fintype.card I)*t r := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hpow (ht r).le
    have hi0 : i ∉ vertices (graph t a K) C := hi
    simp only [paddedAge,paddedCenter,hi0,ite_false,sub_self,abs_zero]
    exact ⟨hdiv hself,le_rfl,mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hK0.le) (Real.sqrt_nonneg _)⟩

theorem representatives_separation (t a : I → ℝ) {K L : ℝ}
    (hstable : ∀ i j, (graph t a K).Reachable i j ↔ (graph t a L).Reachable i j)
    (C D : (graph t a K).ConnectedComponent) (hCD : C ≠ D) :
    t (representative (graph t a K) t C) > L*t (representative (graph t a K) t D) ∨
    t (representative (graph t a K) t D) > L*t (representative (graph t a K) t C) ∨
    |a (representative (graph t a K) t C)-a (representative (graph t a K) t D)| >
      L*Real.sqrt (max (t (representative (graph t a K) t C)) (t (representative (graph t a K) t D))) := by
  have hne := (representative_injective (graph t a K) t).ne hCD
  have hnot : ¬(graph t a L).Adj (representative (graph t a K) t C) (representative (graph t a K) t D) := by
    intro hadj
    have hh := ConnectedComponent.sound ((hstable _ _).mpr hadj.reachable)
    exact hCD (by simpa only [representative_component] using hh)
  by_contra h
  push Not at h
  exact hnot ⟨hne,h.1,h.2.1,h.2.2⟩

end SHE.HeatPartition
