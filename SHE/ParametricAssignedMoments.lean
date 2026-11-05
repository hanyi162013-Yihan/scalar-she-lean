module

public import SHE.UniformFiberMoments
public import SHE.WindowAssignedFactors

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2300000
noncomputable section

namespace SHE.ParametricAssignedMoments
open Set MeasureTheory ProbabilityTheory Real GaussianIncrement GaussianAssignmentBlocks
  ControlledOldIntervals OldIntervalCovariance StoppedGaussianFeatures StoppedFourier ProfileVariance
open scoped BigOperators
local instance : Fact (0<2*π) := ⟨by positivity⟩
variable {Ω : Type*} [MeasurableSpace Ω] {n d r k : ℕ}

def shift (mean : Ω→State n) (z : Ω×((Fin r→State n)×State n)) : (Fin r→State n)×State n :=
  (z.2.1,mean z.1+z.2.2)

theorem shift_measurable (mean : Ω→State n) (hm : Measurable mean) : Measurable (shift (r:=r) mean) :=
  measurable_snd.fst.prodMk ((hm.comp measurable_fst).add measurable_snd.snd)

theorem root_shift (choices : List (Fin r×Fin k)) (factor : Fin k) (F : State d→ℝ)
    (mean : Ω→State n) (g : Fin d→Fin n) (z : Ω×((Fin r→State n)×State n)) :
    VectorControlledRoot.value choices factor F (mean z.1) g z.2=
      VectorControlledRoot.value choices factor F 0 g (shift mean z) := by
  simp only [VectorControlledRoot.value,VectorJointRoot.value,shift,zero_add]

theorem leaf_shift (choices : List (Fin r×Fin k)) (factor : Fin k) (a : ℝ→ℝ)
    (mean : Ω→State n) (i : Fin n) (baseline : ℝ) (z : Ω×((Fin r→State n)×State n)) :
    ControlledAssignedLeaf.leaf choices factor a (mean z.1) i baseline z.2=
      ControlledAssignedLeaf.leaf choices factor a 0 i baseline (shift mean z) := by
  simp only [ControlledAssignedLeaf.leaf,shift]
  congr 3
  funext y
  have he : (0:State n) i+(mean z.1+z.2.2) i=(mean z.1) i+z.2.2 i := by
    change 0+((EuclideanSpace.proj (𝕜:=ℝ) i) (mean z.1+z.2.2))=_
    rw [map_add,zero_add]
    rfl
  rw [he]

theorem root_measurable (choices : List (Fin r×Fin k)) (factor : Fin k) (F : State d→ℝ)
    (hF : Measurable F) (mean : Ω→State n) (hm : Measurable mean) (g : Fin d→Fin n) :
    Measurable (fun z : Ω×((Fin r→State n)×State n) => VectorControlledRoot.value choices factor F (mean z.1) g z.2) := by
  have he : (fun z : Ω×((Fin r→State n)×State n) => VectorControlledRoot.value choices factor F (mean z.1) g z.2)=
      (VectorControlledRoot.value choices factor F 0 g)∘shift mean := funext (root_shift choices factor F mean g)
  rw [he]
  exact (VectorControlledRoot.value_measurable choices factor F hF 0 g).comp (shift_measurable mean hm)

theorem leaf_measurable (choices : List (Fin r×Fin k)) (factor : Fin k) (a : ℝ→ℝ)
    (ha : Measurable a) (mean : Ω→State n) (hm : Measurable mean) (i : Fin n) (baseline : ℝ) :
    Measurable (fun z : Ω×((Fin r→State n)×State n) => ControlledAssignedLeaf.leaf choices factor a (mean z.1) i baseline z.2) := by
  have he : (fun z : Ω×((Fin r→State n)×State n) => ControlledAssignedLeaf.leaf choices factor a (mean z.1) i baseline z.2)=
      (ControlledAssignedLeaf.leaf choices factor a 0 i baseline)∘shift mean := funext (leaf_shift choices factor a mean i baseline)
  rw [he]
  exact (ControlledAssignedLeaf.leaf_measurable choices factor a ha 0 i baseline).comp (shift_measurable mean hm)

/-- An arbitrary dependent measurable current mean does not change any
actual old root clip moment after outer integration. This is proved by
genuine Gaussian Fubini, rather than by assuming independence of factors. -/
theorem root_even_moment (μ : Measure Ω) [IsProbabilityMeasure μ]
    (P : CanonicalCovariance.ProfileParameters) (Λ : ℝ) (u dir : CircleL2)
    (lo hi : Fin r→ℝ) (σ target : Fin n→ℝ) (center : Fin n→HeatCircle)
    (hσ : ∀ i,0<σ i) (hσ1 : ∀ i,σ i≤1) (hages : ∀ i,σ i≤target i)
    (hlo : ∀ j,0≤lo j) (hgap : ∀ j,lo j<hi j)
    (hstop : ∀ j i,σ i≤lo j ∨ hi j≤σ i) (B : Matrix (Fin n) (Fin n) ℝ)
    (mean : Ω→State n) (hm : Measurable mean) (g : Fin d→Fin n)
    (choices : List (Fin r×Fin k)) (hnd : (choices.map Prod.fst).Nodup) (factor : Fin k)
    (F : State d→ℝ) (hFm : Measurable F) {A0 ν : ℝ} (hA0 : 0≤A0) (hν : 0≤ν)
    (hf : ContDiff ℝ (block choices factor).length F)
    (hfb : ∀ j,j≤(block choices factor).length → ∀ z,‖iteratedFDeriv ℝ j F z‖≤A0*ν^j)
    (b : ℕ) (hb : 0<b) :
    let A := familyCovariance σ target center (referenceProfile P Λ u dir) lo hi
    let νG := (Measure.pi (fun j => multivariateGaussian (0:State n) (A j))).prod (multivariateGaussian (0:State n) B)
    Integrable (fun z : Ω×((Fin r→State n)×State n) =>
      |VectorControlledRoot.value choices factor F (mean z.1) g z.2|^(2*b)) (μ.prod νG) ∧
    (∫ z : Ω×((Fin r→State n)×State n),|VectorControlledRoot.value choices factor F (mean z.1) g z.2|^(2*b) ∂μ.prod νG)≤
      ControlledAssignedRoot.constant b choices factor*
        (VectorPhysicalRoot.scale choices factor lo hi A0 ν (P.lower/2) d)^(2*b) := by
  intro A νG
  have hfiber (ω : Ω) := WindowAssignedFactors.root_even_moment P Λ u dir lo hi σ target center hσ hσ1 hages
    hlo hgap hstop B (mean ω) g choices hnd factor F hA0 hν hf hfb b hb
  exact UniformFiberMoments.even_moment μ νG _ (root_measurable choices factor F hFm mean hm g) b _
    (fun ω => (hfiber ω).1) (fun ω => (hfiber ω).2)

end SHE.ParametricAssignedMoments
