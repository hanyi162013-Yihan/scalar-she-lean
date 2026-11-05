module

public import SHE.AgeClustering
public import Mathlib.Data.List.FinRange

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section

namespace SHE.AgeClustering

/-- Ordered separated age groups with actual member representatives. -/
structure Partition {n : ℕ} (s : Fin n → ℝ) (A : ℝ) where
  count : ℕ
  count_le : count ≤ n
  label : Fin n → Fin count
  rep : Fin count → Fin n
  label_rep : ∀ j,label (rep j)=j
  lower : Fin count → ℝ
  upper : Fin count → ℝ
  lower_eq_rep : ∀ j,lower j=s (rep j)
  lower_pos : ∀ j,0 < lower j
  lower_le_upper : ∀ j,lower j ≤ upper j
  lower_bound : ∀ i,lower (label i) ≤ s i
  upper_bound : ∀ i,s i ≤ upper (label i)
  ratio : ∀ j,upper j ≤ A^n*lower j
  separation : ∀ j k,j < k → A*upper j ≤ lower k

/-- Any finite positive age family has an ordered separated partition
whose within-block ratios grow by at most A^n. -/
theorem exists_partition {n : ℕ} (s : Fin n → ℝ) (hpos : ∀ i,0 < s i)
    {A : ℝ} (hA : 1 ≤ A) : Nonempty (Partition s A) := by
  classical
  obtain ⟨bs,hperm,hcount,hbound,hsep⟩ := blocks s hA (List.finRange n) (fun i _ => hpos i)
  have hlen : (List.finRange n).length=n := by simp
  have hbound' : ∀ j : Fin bs.length,BlockBound s A n (bs.get j) := by
    intro j
    simpa only [hlen] using hbound (bs.get j) (bs.get_mem j)
  simp only [BlockBound] at hbound'
  choose lo hlo hi hhi hloPos hwithin hratio using hbound'
  have hindex : ∀ i : Fin n,∃ j : Fin bs.length,i ∈ bs.get j := by
    intro i
    have hmem : i ∈ bs.flatten := hperm.mem_iff.mpr (by simp)
    obtain ⟨B,hB,hiB⟩ := List.mem_flatten.mp hmem
    obtain ⟨j,hj⟩ := List.mem_iff_get.mp hB
    exact ⟨j,hj ▸ hiB⟩
  choose label hlabel using hindex
  have hnodup : bs.flatten.Nodup := hperm.nodup_iff.mpr (List.nodup_finRange n)
  have hdisj := (List.nodup_flatten.mp hnodup).2
  have hunique (j k : Fin bs.length) (i : Fin n) (hj : i ∈ bs.get j) (hk : i ∈ bs.get k) : j=k := by
    rcases lt_trichotomy j k with hlt | heq | hgt
    · exact ((hdisj.rel_get_of_lt hlt) hj hk).elim
    · exact heq
    · exact ((hdisj.rel_get_of_lt hgt) hk hj).elim
  refine ⟨{
    count := bs.length
    count_le := by simpa only [hlen] using hcount
    label := label
    rep := lo
    label_rep := fun j => hunique (label (lo j)) j (lo j) (hlabel (lo j)) (hlo j)
    lower := fun j => s (lo j)
    upper := fun j => s (hi j)
    lower_eq_rep := fun _ => rfl
    lower_pos := hloPos
    lower_le_upper := fun j => (hwithin j (hi j) (hhi j)).1
    lower_bound := fun i => (hwithin (label i) i (hlabel i)).1
    upper_bound := fun i => (hwithin (label i) i (hlabel i)).2
    ratio := hratio
    separation := fun j k hjk => (hsep.rel_get_of_lt hjk) (hi j) (hhi j) (lo k) (hlo k)
  }⟩

theorem Partition.count_pos {n : ℕ} {s : Fin n → ℝ} {A : ℝ}
    (P : Partition s A) (hn : 0 < n) : 0 < P.count :=
  lt_of_le_of_lt (Nat.zero_le (P.label ⟨0,hn⟩).val) (P.label ⟨0,hn⟩).isLt

end SHE.AgeClustering
