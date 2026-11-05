module

public import SHEStochastic.MatrixPhysicalColumnStructure
public import SHEStochastic.MatrixActualColumnCalculus
public import SHEStochastic.JetLinearConstraints

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
noncomputable section

namespace SHEStochastic.MatrixPhysicalJetStructure
open MeasureTheory MatrixInfiniteHaar MatrixPhysicalColumnSmooth MatrixActualColumnCalculus
open scoped NNReal ENNReal MatrixOrder Matrix.Norms.L2Operator ContDiff Topology
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
variable {d : Type*} [Fintype d] [DecidableEq d]
local notation "μ" => AddCircle.haarAddCircle (T := (1 : ℝ))

def jetColumn (P : Profile d) (p : List Bool) (i : d) (w : List (Domain (d := d))) : Physical (d := d) :=
  DirectionalJets.jet w (fun z : Domain (d := d) =>
    MatrixPhysicalColumnMap.detail (MatrixGlobalHaar.child p false) (MatrixGlobalHaar.child p true)
      (MatrixGlobalHaar.child_measurable p false) (MatrixGlobalHaar.child_measurable p true) i z.val)
    (MatrixProfileSymmetry.realize d P)

/-- All actual physical derivative columns retain their exact support
and ordinary spatial cancellation, by proved bounded linear constraints. -/
theorem properties (P : Profile d) (p : List Bool) (i : d) (w : List (Domain (d := d))) :
    SpatialRestriction.operator (SHE.FiniteHaar.nodeCell p) (SHE.FiniteHaar.measurableSet_nodeCell p)
      (jetColumn P p i w)=jetColumn P p i w ∧
    (∫ x, jetColumn P p i w x ∂μ)=0 := by
  let s := MatrixGlobalHaar.child p false
  let t := MatrixGlobalHaar.child p true
  let hs := MatrixGlobalHaar.child_measurable p false
  let ht := MatrixGlobalHaar.child_measurable p true
  let x := MatrixProfileSymmetry.realize d P
  let m := childLength p*P.lower
  let o := neighborhood s t x m
  have ho := neighborhood_open s t x m
  have hx := neighborhood_self s t x m (mul_pos (childLength_pos p) P.lower_pos)
  have hp := neighborhood_positive s t x m (child_positive P p false) (child_positive P p true)
    ⟨child_lower P p false, child_lower P p true⟩
  let f := fun z : Domain (d := d) => MatrixPhysicalColumnMap.detail s t hs ht i z.val
  have hf : ∀ y∈o, ContDiffAt ℝ ∞ f y :=
    detail_contDiff s t hs ht i x m (child_positive P p false) (child_positive P p true)
      ⟨child_lower P p false, child_lower P p true⟩
  let R : Physical (d := d) →L[ℝ] Physical (d := d) := SpatialRestriction.operator (s∪t) (hs.union ht)
  constructor
  · let L := ContinuousLinearMap.id ℝ (Physical (d := d))-R
    have hz : ∀ y∈o, L (f y)=0 := by
      intro y hy
      change f y-R (f y)=0
      rw [MatrixPhysicalColumnStructure.restriction_eq]
      exact sub_self _
    have hh := JetLinearConstraints.zero L o ho x hx f hf hz w
    change DirectionalJets.jet w f x-R (DirectionalJets.jet w f x)=0 at hh
    exact (sub_eq_zero.mp hh).symm
  · let I := SHE.LpIntegralFubini.setIntegralCLM (E := EuclideanSpace ℝ d) μ Set.univ
    have hz : ∀ y∈o, I (f y)=0 := by
      intro y hy
      change (∫ z in Set.univ, MatrixPhysicalColumnMap.detail s t hs ht i y.val z ∂μ)=0
      rw [setIntegral_univ]
      exact MatrixPhysicalColumnStructure.mean_zero s t hs ht y.val i (hp y hy).1 (hp y hy).2
    have hh := JetLinearConstraints.zero I o ho x hx f hf hz w
    change (∫ z in Set.univ, jetColumn P p i w z ∂μ)=0 at hh
    simpa only [setIntegral_univ] using hh

theorem mean_zero (P : Profile d) (p : List Bool) (i : d) (w : List (Domain (d := d))) :
    (∫ x, jetColumn P p i w x ∂μ)=0 := (properties P p i w).2

theorem supported (P : Profile d) (p : List Bool) (i : d) (w : List (Domain (d := d))) :
    ∀ᵐ x ∂μ, x∉SHE.FiniteHaar.nodeCell p → jetColumn P p i w x=0 := by
  have he := (properties P p i w).1
  have hh := SpatialRestriction.operator_ae (SHE.FiniteHaar.nodeCell p)
    (SHE.FiniteHaar.measurableSet_nodeCell p) (jetColumn P p i w)
  rw [he] at hh
  filter_upwards [hh] with x hx
  intro hn
  rw [hx, Set.indicator_of_notMem hn]

end SHEStochastic.MatrixPhysicalJetStructure
