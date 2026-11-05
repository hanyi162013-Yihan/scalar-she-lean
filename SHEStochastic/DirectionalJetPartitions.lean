module

public import SHEStochastic.DirectionalJets

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
noncomputable section

namespace SHEStochastic.DirectionalJets

variable {E A : Type*}

def properPairs (w : List E) : List (List E × List E) :=
  (pairs w).filter (fun p ↦ !p.1.isEmpty && !p.2.isEmpty)

theorem pairs_left_empty (w : List E) : (pairs w).filter (fun p ↦ p.1.isEmpty) = [([],w)] := by
  induction w with
  | nil => rfl
  | cons v w ih =>
    simp only [pairs, List.filter_append, List.filter_map, Function.comp_def,
      List.isEmpty_cons, List.filter_false, List.map_nil, List.nil_append]
    rw [ih]
    rfl

theorem pairs_right_empty (w : List E) : (pairs w).filter (fun p ↦ p.2.isEmpty) = [(w,[])] := by
  induction w with
  | nil => rfl
  | cons v w ih =>
    simp only [pairs, List.filter_append, List.filter_map, Function.comp_def,
      List.isEmpty_cons, List.filter_false, List.map_nil, List.append_nil]
    rw [ih]
    rfl

theorem pairs_length (w : List E) (p : List E × List E) (hp : p∈pairs w) :
    p.1.length+p.2.length=w.length := by
  induction w generalizing p with
  | nil =>
    change p∈[([],[])] at hp
    have he := List.mem_singleton.mp hp
    subst p
    rfl
  | cons v w ih =>
    rcases List.mem_append.mp hp with h | h
    · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp h
      have hh := ih q hq
      simp only [List.length_cons]
      omega
    · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp h
      have hh := ih q hq
      simp only [List.length_cons]
      omega

/-- Every factor in the proper mixed remainder has strictly lower
order than the differentiated product. -/
theorem proper_lower (w : List E) (p : List E × List E) (hp : p∈properPairs w) :
    0<p.1.length ∧ p.1.length<w.length ∧ 0<p.2.length ∧ p.2.length<w.length := by
  have hmem := List.mem_filter.mp hp
  have hl := pairs_length w p hmem.1
  have hh : !p.1.isEmpty && !p.2.isEmpty = true := hmem.2
  have hne1 : p.1≠[] := by intro he; simp [he] at hh
  have hne2 : p.2≠[] := by intro he; simp [he] at hh
  have h1 : p.1.length≠0 := fun he ↦ hne1 (List.length_eq_zero_iff.mp he)
  have h2 : p.2.length≠0 := fun he ↦ hne2 (List.length_eq_zero_iff.mp he)
  omega

variable [AddCommMonoid A]

theorem sum_partition {X : Type*} (l : List X) (b : X → Bool) (f : X → A) :
    (l.map f).sum = ((l.filter b).map f).sum + ((l.filter (fun x ↦ !b x)).map f).sum := by
  induction l with
  | nil => simp only [List.map_nil, List.sum_nil, List.filter_nil, add_zero]
  | cons x l ih =>
    cases h : b x <;> simp [List.filter_cons, h, ih, add_assoc, add_left_comm, add_comm]

/-- The two endpoint terms are separated from the proper mixed terms,
with no commutation of multiplication required by the application. -/
theorem sum_pairs_split (w : List E) (hw : w≠[]) (f : List E × List E → A) :
    ((pairs w).map f).sum = f ([],w)+f (w,[]) + ((properPairs w).map f).sum := by
  have hl := sum_partition (pairs w) (fun p ↦ p.1.isEmpty) f
  rw [pairs_left_empty] at hl
  have hr := sum_partition ((pairs w).filter (fun p ↦ !p.1.isEmpty)) (fun p ↦ p.2.isEmpty) f
  have hright : (((pairs w).filter (fun p ↦ !p.1.isEmpty)).filter (fun p ↦ p.2.isEmpty)) = [(w,[])] := by
    rw [List.filter_comm, pairs_right_empty]
    simp [hw]
  have hproper : (((pairs w).filter (fun p ↦ !p.1.isEmpty)).filter (fun p ↦ !p.2.isEmpty)) = properPairs w := by
    simp only [properPairs, List.filter_filter, Bool.and_comm]
  rw [hright, hproper] at hr
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero] at hl hr
  rw [hl, hr]
  exact (add_assoc _ _ _).symm

end SHEStochastic.DirectionalJets
