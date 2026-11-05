module

public import SHEStochastic.MatrixHigherHeat

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
noncomputable section

namespace SHEStochastic.MatrixRootCalculus
open MeasureTheory Matrix MatrixInfiniteHaar MatrixPhysicalColumnSmooth MatrixProfileHilbert Filter
open MatrixFrobeniusNorm MatrixJetClosure
open scoped NNReal ENNReal MatrixOrder Matrix.Norms.L2Operator ContDiff Topology
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local notation "μ" => AddCircle.haarAddCircle (T := (1 : ℝ))
variable {d : Type*} [Fintype d] [DecidableEq d]

def total : Domain (d := d) →L[ℝ] Matrix d d ℝ := MatrixPhysicalColumnSmooth.mass Set.univ
def coefficient (u : Domain (d := d)) := MatrixFiniteHaar.inverseSqrt (total u)
def root (i : d) (u : Domain (d := d)) : Physical (d := d) :=
  MatrixPhysicalColumnMap.action i u.val (coefficient u)

theorem total_realize (P : Profile d) :
    total (MatrixProfileSymmetry.realize d P) = ∫ x, P.value x ∂μ := by
  change MatrixProfileHilbert.mass d Set.univ (MatrixProfileHilbert.realize d P) = _
  rw [mass_realize, MatrixHaarFunctions.mass, setIntegral_univ]

theorem lower (P : Profile d) :
    P.lower • (1 : Matrix d d ℝ) ≤ total (MatrixProfileSymmetry.realize d P) := by
  have hh := MatrixHaarMass.lower μ P.value P.integrable P.lower P.lower_bound Set.univ
  simpa [MatrixHaarFunctions.mass, total_realize, Measure.real] using hh

theorem positive (P : Profile d) : (total (MatrixProfileSymmetry.realize d P)).PosDef := by
  rw [total_realize]
  have hh := MatrixHaarMass.posDef μ P.value P.integrable P.lower P.lower_pos P.lower_bound Set.univ
    (by simp : 0 < μ Set.univ)
  simpa only [MatrixHaarFunctions.mass, setIntegral_univ] using hh

def region (P : Profile d) := neighborhood Set.univ Set.univ (MatrixProfileSymmetry.realize d P) P.lower

theorem region_open (P : Profile d) : IsOpen (region P) := neighborhood_open _ _ _ _
theorem region_self (P : Profile d) : MatrixProfileSymmetry.realize d P ∈ region P :=
  neighborhood_self _ _ _ _ P.lower_pos
theorem region_positive (P : Profile d) : ∀ u ∈ region P, (total u).PosDef :=
  fun u hu => (neighborhood_positive _ _ _ _ (positive P) (positive P) ⟨lower P, lower P⟩ u hu).1

theorem smooth (P : Profile d) : ∀ y ∈ region P, ContDiffAt ℝ ∞ coefficient y := by
  intro y hy
  have hm : ContDiffAt ℝ ∞ (fun z : Domain (d := d) => total z) y := by
    convert! (total (d := d)).contDiff.contDiffAt using 1
  have hp := region_positive P
  have he : ∀ᶠ z in 𝓝 y, z ∈ region P := (region_open P).mem_nhds hy
  have hs := MatrixSqrtSmooth.comp hm (hp y hy)
    (he.mono (fun z hz => (hp z hz).posSemidef.nonneg))
  exact MatrixHaarSmooth.inverse hs (MatrixHaarPositive.sqrt_posDef _ (hp y hy)).isUnit

def baseConstant (d : Type*) [Fintype d] (m : ℝ) : ℝ :=
  MatrixHaarJetBounds.inverseSize d (Real.sqrt m)
def derivativeConstant (d : Type*) [Fintype d] (m : ℝ) : ℕ → ℝ :=
  inverseConstant (baseConstant d m) (rootConstant (Real.sqrt m) (fun _ => 1))
def constant (d : Type*) [Fintype d] (m : ℝ) (n : ℕ) : ℝ :=
  max (baseConstant d m) (derivativeConstant d m n)
def perturbation (v : Domain (d := d)) : ℝ := size (total v)

theorem constant_nonnegative (P : Profile d) (n : ℕ) : 0 ≤ constant d P.lower n :=
  (inverseConstant_nonneg _ _ n).trans (le_max_right _ _)
theorem perturbation_nonnegative (v : Domain (d := d)) : 0 ≤ perturbation v := nonneg _

theorem coefficient_jets (P : Profile d) (w : List (Domain (d := d))) :
    size (DirectionalJets.jet w coefficient (MatrixProfileSymmetry.realize d P)) ≤
      constant d P.lower w.length * weight perturbation w := by
  let x := MatrixProfileSymmetry.realize d P
  let A := fun y : Domain (d := d) => total y
  let T := fun y : Domain (d := d) => CFC.sqrt (A y)
  let s := region P
  have hs := region_open P
  have hx := region_self P
  have hp : ∀ y ∈ s, (A y).PosDef := region_positive P
  have hA : ∀ y ∈ s, ContDiffAt ℝ ∞ A y := by
    intro y hy
    convert! (total (d := d)).contDiff.contDiffAt using 1
  have hT : ∀ y ∈ s, ContDiffAt ℝ ∞ T y := by
    intro y hy
    have he : ∀ᶠ z in 𝓝 y, z ∈ s := hs.mem_nhds hy
    exact MatrixSqrtSmooth.comp (hA y hy) (hp y hy)
      (he.mono (fun z hz => (hp z hz).posSemidef.nonneg))
  have hr := Real.sqrt_pos.mpr P.lower_pos
  have hLo : (Real.sqrt P.lower) ^ 2 • (1 : Matrix d d ℝ) ≤ A x := by
    rw [Real.sq_sqrt P.lower_pos.le]
    exact lower P
  have hInv : size ((T x)⁻¹) ≤ baseConstant d P.lower :=
    MatrixEllipticSize.inverse_sqrt (A x) (positive P) _ hr hLo
  have hInput : ∀ z : List (Domain (d := d)), z ≠ [] → size (DirectionalJets.jet z A x) ≤
      (1 : ℝ) * weight perturbation z := by
    intro z hz
    simpa only [A, zero_add, one_mul] using MatrixJetClosure.affine 0 total perturbation perturbation_nonnegative
      (fun v => le_rfl) x z hz
  by_cases hw : w = []
  · subst w
    simp only [DirectionalJets.jet, weight, List.map_nil, List.prod_nil, List.length_nil, mul_one]
    exact hInv.trans (le_max_left _ _)
  · have hh := MatrixJetClosure.inverse T perturbation perturbation_nonnegative
      (rootConstant (Real.sqrt P.lower) (fun _ => 1)) (rootConstant_nonneg _ _) (rootConstant_mono _ _)
      s hs hT (fun y hy => (MatrixHaarPositive.sqrt_posDef _ (hp y hy)).isUnit) x hx _ hInv
      (fun z hz => MatrixJetClosure.sqrt A perturbation perturbation_nonnegative (fun _ => 1)
        s hs hA hp x hx _ hr hLo hInput z hz) w hw
    exact hh.trans (mul_le_mul_of_nonneg_right (le_max_right _ _)
      (weight_nonneg perturbation perturbation_nonnegative w))

end SHEStochastic.MatrixRootCalculus
