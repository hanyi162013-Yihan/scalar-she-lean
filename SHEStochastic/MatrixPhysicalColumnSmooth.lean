module

public import SHEStochastic.MatrixPhysicalColumnMap
public import SHEStochastic.MatrixProfileSymmetry
public import SHEStochastic.MatrixPositiveCoordinates

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
noncomputable section

namespace SHEStochastic.MatrixPhysicalColumnSmooth
open MeasureTheory Matrix MatrixInfiniteHaar Filter
open scoped NNReal ENNReal MatrixOrder Matrix.Norms.L2Operator ContDiff Topology

local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
variable {d : Type*} [Fintype d] [DecidableEq d]
local notation "μ" => AddCircle.haarAddCircle (T := (1 : ℝ))
abbrev Domain := MatrixProfileSymmetry.symmetric d

def mass (s : Set (AddCircle (1 : ℝ))) : Domain (d := d) →L[ℝ] Matrix d d ℝ :=
  (MatrixProfileHilbert.mass d s).comp (MatrixProfileSymmetry.symmetric d).subtypeL

def restricted (s : Set (AddCircle (1 : ℝ))) (hs : MeasurableSet s) :
    Domain (d := d) →L[ℝ] MatrixProfileHilbert.Space d :=
  (MatrixPhysicalColumnMap.restriction s hs).comp (MatrixProfileSymmetry.symmetric d).subtypeL

def neighborhood (s t : Set (AddCircle (1 : ℝ))) (x : Domain (d := d)) (m : ℝ) : Set (Domain (d := d)) :=
  {y | ‖mass s (y-x)‖ < m ∧ ‖mass t (y-x)‖ < m}

theorem neighborhood_open (s t : Set (AddCircle (1 : ℝ))) (x : Domain (d := d)) (m : ℝ) :
    IsOpen (neighborhood s t x m) :=
  (isOpen_lt (((mass s).continuous.comp (continuous_id.sub continuous_const)).norm) continuous_const).inter
    (isOpen_lt (((mass t).continuous.comp (continuous_id.sub continuous_const)).norm) continuous_const)

theorem neighborhood_self (s t : Set (AddCircle (1 : ℝ))) (x : Domain (d := d))
    (m : ℝ) (hm : 0 < m) : x∈neighborhood s t x m := by
  simp only [neighborhood, Set.mem_setOf_eq, sub_self, map_zero, norm_zero]
  exact ⟨hm, hm⟩

theorem neighborhood_positive (s t : Set (AddCircle (1 : ℝ))) (x : Domain (d := d))
    (m : ℝ) (hA : (mass s x).PosDef) (hB : (mass t x).PosDef)
    (hLo : m • (1 : Matrix d d ℝ) ≤ mass s x ∧ m • (1 : Matrix d d ℝ) ≤ mass t x) :
    ∀ y∈neighborhood s t x m, (mass s y).PosDef ∧ (mass t y).PosDef := by
  intro y hy
  have he (s : Set (AddCircle (1 : ℝ))) : mass s x+mass s (y-x)=mass s y := by
    rw [map_sub]
    abel
  constructor
  · have hh := MatrixPositiveCoordinates.positive (mass s x) (mass s (y-x)) hA
      (MatrixProfileSymmetry.mass_hermitian d s (y-x)) m hLo.1 hy.1
    rwa [he] at hh
  · have hh := MatrixPositiveCoordinates.positive (mass t x) (mass t (y-x)) hB
      (MatrixProfileSymmetry.mass_hermitian d t (y-x)) m hLo.2 hy.2
    rwa [he] at hh

theorem children_contDiff (s t : Set (AddCircle (1 : ℝ))) (x : Domain (d := d))
    (m : ℝ) (hA : (mass s x).PosDef) (hB : (mass t x).PosDef)
    (hLo : m • (1 : Matrix d d ℝ) ≤ mass s x ∧ m • (1 : Matrix d d ℝ) ≤ mass t x) :
    ∀ y∈neighborhood s t x m,
      ContDiffAt ℝ ∞ (fun z => MatrixHaarAlgebra.left (mass s z) (mass t z)) y ∧
      ContDiffAt ℝ ∞ (fun z => MatrixHaarAlgebra.right (mass s z) (mass t z)) y := by
  intro y hy
  have hp := neighborhood_positive s t x m hA hB hLo
  have hL : ContDiffAt ℝ ∞ (fun z => mass s z) y := by
    convert! (mass (d := d) s).contDiff.contDiffAt using 1
  have hR : ContDiffAt ℝ ∞ (fun z => mass t z) y := by
    convert! (mass (d := d) t).contDiff.contDiffAt using 1
  have he : ∀ᶠ z in 𝓝 y, z∈neighborhood s t x m := (neighborhood_open s t x m).mem_nhds hy
  exact MatrixHaarSmooth.children (k := ∞) hL hR (hp y hy).1 (hp y hy).2
    (he.mono (fun z hz => hp z hz))

/-- Actual physical detail columns have a smooth local extension to
the symmetric Frobenius `L²` profile space. Only the two interval
masses need stay positive; positivity of all pointwise profiles is not
incorrectly assumed open in the `L²` topology. -/
theorem detail_contDiff (s t : Set (AddCircle (1 : ℝ))) (hs : MeasurableSet s) (ht : MeasurableSet t)
    (i : d) (x : Domain (d := d)) (m : ℝ) (hA : (mass s x).PosDef) (hB : (mass t x).PosDef)
    (hLo : m • (1 : Matrix d d ℝ) ≤ mass s x ∧ m • (1 : Matrix d d ℝ) ≤ mass t x) :
    ∀ y∈neighborhood s t x m,
      ContDiffAt ℝ ∞ (fun z : Domain (d := d) => MatrixPhysicalColumnMap.detail s t hs ht i z.val) y := by
  intro y hy
  have hc := children_contDiff s t x m hA hB hLo y hy
  exact (DirectionalJets.bilinear_smooth (MatrixPhysicalColumnMap.action i)
    (restricted s hs).contDiff.contDiffAt hc.1).add
      (DirectionalJets.bilinear_smooth (MatrixPhysicalColumnMap.action i)
        (restricted t ht).contDiff.contDiffAt hc.2)

/-- Exact all-order physical column derivatives. The omission list
retains each differentiation position, so every term contains at most
one unaveraged profile direction. All derivatives are actual jets. -/
theorem detail_jets (s t : Set (AddCircle (1 : ℝ))) (hs : MeasurableSet s) (ht : MeasurableSet t)
    (i : d) (x : Domain (d := d)) (m : ℝ) (hm : 0 < m)
    (hA : (mass s x).PosDef) (hB : (mass t x).PosDef)
    (hLo : m • (1 : Matrix d d ℝ) ≤ mass s x ∧ m • (1 : Matrix d d ℝ) ≤ mass t x)
    (w : List (Domain (d := d))) :
    DirectionalJets.jet w (fun z : Domain (d := d) => MatrixPhysicalColumnMap.detail s t hs ht i z.val) x=
      MatrixPhysicalColumnMap.action i (restricted s hs x)
        (DirectionalJets.jet w (fun z => MatrixHaarAlgebra.left (mass s z) (mass t z)) x)+
      ((DirectionalJets.omissions w).map (fun p => MatrixPhysicalColumnMap.action i (restricted s hs p.1)
        (DirectionalJets.jet p.2 (fun z => MatrixHaarAlgebra.left (mass s z) (mass t z)) x))).sum+
      (MatrixPhysicalColumnMap.action i (restricted t ht x)
        (DirectionalJets.jet w (fun z => MatrixHaarAlgebra.right (mass s z) (mass t z)) x)+
      ((DirectionalJets.omissions w).map (fun p => MatrixPhysicalColumnMap.action i (restricted t ht p.1)
        (DirectionalJets.jet p.2 (fun z => MatrixHaarAlgebra.right (mass s z) (mass t z)) x))).sum) := by
  let o := neighborhood s t x m
  have ho := neighborhood_open s t x m
  have hx := neighborhood_self s t x m hm
  have hc := children_contDiff s t x m hA hB hLo
  have hl := DirectionalJets.affine_bilinear (MatrixPhysicalColumnMap.action i) 0 (restricted s hs)
    o ho x hx w _ (fun y hy => (hc y hy).1)
  have hr := DirectionalJets.affine_bilinear (MatrixPhysicalColumnMap.action i) 0 (restricted t ht)
    o ho x hx w _ (fun y hy => (hc y hy).2)
  have hh := DirectionalJets.add o ho x hx w
    (fun z => MatrixPhysicalColumnMap.action i (restricted s hs z) (MatrixHaarAlgebra.left (mass s z) (mass t z)))
    (fun z => MatrixPhysicalColumnMap.action i (restricted t ht z) (MatrixHaarAlgebra.right (mass s z) (mass t z)))
    (fun y hy => DirectionalJets.bilinear_smooth _ (restricted s hs).contDiff.contDiffAt (hc y hy).1)
    (fun y hy => DirectionalJets.bilinear_smooth _ (restricted t ht).contDiff.contDiffAt (hc y hy).2)
  simp only [zero_add] at hl hr
  rw [hl, hr] at hh
  exact hh

end SHEStochastic.MatrixPhysicalColumnSmooth
