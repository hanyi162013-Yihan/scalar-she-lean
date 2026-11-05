module

public import SHEStochastic.MatrixProfileInterpolation
public import Mathlib.Analysis.Calculus.MeanValue

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section

namespace SHEStochastic.MatrixColumnComparison
open MeasureTheory SHE SHE.FiniteHaar MatrixInfiniteHaar MatrixPhysicalColumnSmooth MatrixProfileInterpolation
open scoped NNReal ENNReal MatrixOrder Matrix.Norms.L2Operator ContDiff
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
variable {d : Type*} [Fintype d] [DecidableEq d]

theorem smooth (P : Profile d) (i : d) (q : HaarNode) :
    ContDiffAt ℝ ∞ (MatrixHaarHigherFamily.column i q) (MatrixProfileSymmetry.realize d P) := by
  cases q with
  | none =>
    have hf : ContDiffAt ℝ ∞ (fun u : Domain (d := d) => u.val) (MatrixProfileSymmetry.realize d P) :=
      (MatrixProfileSymmetry.symmetric d).subtypeL.contDiff.contDiffAt
    exact DirectionalJets.bilinear_smooth (MatrixPhysicalColumnMap.action i) hf
      (MatrixRootCalculus.smooth P _ (MatrixRootCalculus.region_self P))
  | some p => exact MatrixActualColumnCalculus.smooth P p i

def difference (P Q : Profile d) : Domain (d := d) :=
  MatrixProfileSymmetry.realize d Q - MatrixProfileSymmetry.realize d P
def path (P Q : Profile d) (s : ℝ) : Domain (d := d) :=
  MatrixProfileSymmetry.realize d P + s • difference P Q
theorem path_zero (P Q : Profile d) : path P Q 0 = MatrixProfileSymmetry.realize d P := by simp [path]
theorem path_one (P Q : Profile d) : path P Q 1 = MatrixProfileSymmetry.realize d Q := by simp [path, difference]
def detailConstant (P Q : Profile d) : ℝ :=
  MatrixOneInputColumn.orderConstant (blend P Q 0 ⟨le_rfl, zero_le_one⟩) 0
def rootConstant (P Q : Profile d) : ℝ :=
  MatrixRootJets.orderConstant (blend P Q 0 ⟨le_rfl, zero_le_one⟩) 0

theorem path_smooth (P Q : Profile d) (i : d) (q : HaarNode) (s : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    ContDiffAt ℝ ∞ (MatrixHaarHigherFamily.column i q) (path P Q s) := by
  have hh := smooth (blend P Q s hs) i q
  rw [realize_line] at hh
  exact hh

theorem hasDerivAt (P Q : Profile d) (i : d) (q : HaarNode) (s : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    HasDerivAt (fun r => MatrixHaarHigherFamily.column i q (path P Q r))
      (DirectionalJets.jet [difference P Q] (MatrixHaarHigherFamily.column i q) (path P Q s)) s := by
  have hline : HasDerivAt (path P Q) (difference P Q) s := by
    have hh := ((hasDerivAt_id s).smul_const (difference P Q)).const_add (MatrixProfileSymmetry.realize d P)
    simp only [id_eq, one_smul] at hh
    convert! hh using 1
  exact ((path_smooth P Q i q s hs).differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt s hline

/-- Integrating the proved physical derivative gives a local signed
column bound for two arbitrary bounded elliptic matrix profiles. -/
theorem detail (P Q : Profile d) (p : List Bool) (i : d) :
    ‖MatrixHaarHigherFamily.column i (some p) (MatrixProfileSymmetry.realize d Q) -
      MatrixHaarHigherFamily.column i (some p) (MatrixProfileSymmetry.realize d P)‖ ≤
      2 * (Real.sqrt (MatrixActualColumnCalculus.childLength p))⁻¹ * detailConstant P Q *
        MatrixDirectionBounds.localSize p (difference P Q) := by
  have hh := norm_image_sub_le_of_norm_deriv_le_segment_01'
    (C := 2 * (Real.sqrt (MatrixActualColumnCalculus.childLength p))⁻¹ * detailConstant P Q *
      MatrixDirectionBounds.localSize p (difference P Q))
    (fun s hs => (hasDerivAt P Q i (some p) s hs).hasDerivWithinAt) (by
      intro s hs
      have hs' : s ∈ Set.Icc (0 : ℝ) 1 := ⟨hs.1, hs.2.le⟩
      have hb := MatrixOneInputColumn.local_L2 (blend P Q s hs') p i (difference P Q) []
        (fun _ => (0 : ℝ)) (fun _ => le_rfl) (by simp)
      rw [realize_line] at hb
      simp only [MatrixJetClosure.weight, List.map_nil, List.prod_nil, List.length_nil, mul_one] at hb
      convert! hb using 1)
  simpa only [path_one, path_zero] using hh

theorem root (P Q : Profile d) (i : d) :
    ‖MatrixHaarHigherFamily.column i none (MatrixProfileSymmetry.realize d Q) -
      MatrixHaarHigherFamily.column i none (MatrixProfileSymmetry.realize d P)‖ ≤
      rootConstant P Q * ‖difference P Q‖ := by
  have hh := norm_image_sub_le_of_norm_deriv_le_segment_01'
    (C := rootConstant P Q * ‖difference P Q‖)
    (fun s hs => (hasDerivAt P Q i none s hs).hasDerivWithinAt) (by
      intro s hs
      have hs' : s ∈ Set.Icc (0 : ℝ) 1 := ⟨hs.1, hs.2.le⟩
      have hb := MatrixRootJets.one_input (blend P Q s hs') i (difference P Q) []
        (fun _ => (0 : ℝ)) (fun _ => le_rfl) (by simp)
      rw [realize_line] at hb
      simp only [MatrixJetClosure.weight, List.map_nil, List.prod_nil, List.length_nil, mul_one] at hb
      convert! hb using 1)
  simpa only [path_one, path_zero] using hh

end SHEStochastic.MatrixColumnComparison
