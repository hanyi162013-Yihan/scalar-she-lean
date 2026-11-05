module

public import SHEStochastic.MatrixColumnComparison
public import SHEStochastic.HilbertColumnMVT
public import SHEStochastic.DirectionalJetCommutation

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
noncomputable section

namespace SHEStochastic.MatrixJetSegment
open SHE SHE.FiniteHaar MatrixInfiniteHaar MatrixPhysicalColumnSmooth MatrixColumnComparison MatrixProfileInterpolation
variable {d E : Type*} [Fintype d] [DecidableEq d] [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- One common segment argument for all actual matrix column jets and
all bounded output transforms. Uniform derivative energy is sufficient;
no regularity of an infinite column-valued map is assumed. -/
theorem energy (P Q : Profile d) (w : List (Domain (d := d))) (T : Physical (d := d) →L[ℝ] E)
    (C : ℝ) (hC : 0 ≤ C)
    (ha : ∀ (s : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) 1),
      Summable (fun k => ‖T (MatrixHaarHigherFamily.jet (blend P Q s hs) (difference P Q :: w) k)‖^2) ∧
        (∑' k, ‖T (MatrixHaarHigherFamily.jet (blend P Q s hs) (difference P Q :: w) k)‖^2) ≤ C) :
    Summable (fun k => ‖T (MatrixHaarHigherFamily.jet Q w k - MatrixHaarHigherFamily.jet P w k)‖^2) ∧
      (∑' k, ‖T (MatrixHaarHigherFamily.jet Q w k - MatrixHaarHigherFamily.jet P w k)‖^2) ≤ C := by
  let F := fun (k : d × HaarNode) (s : ℝ) => T (DirectionalJets.jet w (MatrixHaarHigherFamily.column k.1 k.2) (path P Q s))
  let A := fun (k : d × HaarNode) (s : ℝ) =>
    T (DirectionalJets.jet (difference P Q :: w) (MatrixHaarHigherFamily.column k.1 k.2) (path P Q s))
  have hD (k : d × HaarNode) (s : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) 1) : HasDerivAt (F k) (A k s) s :=
    T.hasFDerivAt.comp_hasDerivAt s (DirectionalJets.hasDerivAt_line
      (MatrixProfileSymmetry.realize d P) (difference P Q) s (path_smooth P Q k.1 k.2 s hs) w)
  have hb (s : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) 1) : Summable (fun k => ‖A k s‖^2) ∧ (∑' k, ‖A k s‖^2) ≤ C := by
    have he (k : d × HaarNode) : A k s = T (MatrixHaarHigherFamily.jet (blend P Q s hs) (difference P Q :: w) k) := by
      dsimp only [MatrixHaarHigherFamily.jet]
      rw [realize_line]
      rfl
    simpa only [he] using ha s hs
  have hh := HilbertColumnMVT.energy F A C hC hD (fun s hs => (hb s hs).1) (fun s hs => (hb s hs).2)
  have he (k : d × HaarNode) : F k 1 - F k 0 = T (MatrixHaarHigherFamily.jet Q w k - MatrixHaarHigherFamily.jet P w k) := by
    dsimp only [F]
    rw [path_one, path_zero, ← map_sub]
    rfl
  simpa only [he] using hh

end SHEStochastic.MatrixJetSegment
