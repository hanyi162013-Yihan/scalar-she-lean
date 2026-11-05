module

public import SHE.ControlledAssignedLeaf

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
noncomputable section

namespace SHE.ControlledAssignedRoot
open Set MeasureTheory ProbabilityTheory Real GaussianIncrement GaussianAssignmentBlocks
  GaussianVectorFractions GaussianRoughBlocks GaussianRoughBlockMoments JointGaussianBlocks
  GaussianClipMoments ControlledOldIntervals OldIntervalCovariance StoppedGaussianFeatures
  StoppedFourier ProfileVariance
open scoped BigOperators
local instance : Fact (0 < 2 * π) := ⟨by positivity⟩
variable {n r k : ℕ}

def root (choices : List (Fin r × Fin k)) (factor : Fin k) (f : ℝ → ℝ)
    (m : State n) (coordinate : Fin n) : (Fin r → State n) × State n → ℝ :=
  jointBlock choices factor f (fun y => m coordinate + y coordinate)
    (fun _ => EuclideanSpace.proj (𝕜 := ℝ) coordinate)

def constant (p : ℕ) (choices : List (Fin r × Fin k)) (factor : Fin k) : ℝ :=
  if block choices factor = [] then 1 else clipMomentConstant (p*(block choices factor).length)

def scale (P : CanonicalCovariance.ProfileParameters) (choices : List (Fin r × Fin k)) (factor : Fin k)
    (lo hi : Fin r → ℝ) (A0 ν : ℝ) : ℝ :=
  (2 : ℝ)^((block choices factor).length)*A0*
    (∏ j : Fin (block choices factor).length, min 1
      (ν*sqrt (upperConstant*(P.lower/2))*
        (hi ((block choices factor).get j)-lo ((block choices factor).get j))^(1/4 : ℝ)))

theorem constant_nonneg (p : ℕ) (choices : List (Fin r × Fin k)) (factor : Fin k) :
    0 ≤ constant p choices factor := by
  unfold constant
  split_ifs
  · norm_num
  · exact clipMomentConstant_nonneg _

theorem scale_nonneg (P : CanonicalCovariance.ProfileParameters) (choices : List (Fin r × Fin k))
    (factor : Fin k) (lo hi : Fin r → ℝ) (hgap : ∀ j, lo j ≤ hi j)
    {A0 ν : ℝ} (hA0 : 0 ≤ A0) (hν : 0 ≤ ν) :
    0 ≤ scale P choices factor lo hi A0 ν := by
  unfold scale
  apply mul_nonneg (mul_nonneg (by positivity) hA0)
  exact Finset.prod_nonneg (fun j _ => le_min (by norm_num)
    (mul_nonneg (mul_nonneg hν (sqrt_nonneg _)) (rpow_nonneg (sub_nonneg.mpr (hgap _)) _)))

/-- Actual physical root-block moments at all assignment orders, including
the unassigned bounded root. Every original old-gap clip is retained. -/
theorem root_even_moment (P : CanonicalCovariance.ProfileParameters)
    (Λ : ℝ) (u d : CircleL2) (θ : ℝ) (lo hi : Fin r → ℝ)
    (target : Fin n → ℝ) (center : Fin n → HeatCircle)
    (ht : ∀ i, target i ∈ Ioc 0 P.horizon) (hlo : ∀ j, 0 ≤ lo j) (hgap : ∀ j, lo j < hi j)
    (hstop : ∀ j i, target i ≤ lo j ∨ hi j ≤ target i)
    (m : State n) (choices : List (Fin r × Fin k)) (hnd : (choices.map Prod.fst).Nodup)
    (factor : Fin k) (coordinate : Fin n) (f : ℕ → ℝ → ℝ) (hfm : Measurable (f 0))
    {A0 ν : ℝ} (hA0 : 0 ≤ A0) (hν : 0 ≤ ν)
    (hf : ∀ j, j < (block choices factor).length → ∀ z, HasDerivAt (f j) (f (j+1) z) z)
    (hfb : ∀ j, j ≤ (block choices factor).length → ∀ z, |f j z| ≤ A0*ν^j) (p : ℕ) :
    let A := familyCovariance target target center (referenceProfile P Λ u d) lo hi
    let B := ControlledFixedReserve.covariance P Λ u d (fixedProfile P Λ u d lo hi)
      target target center 0 θ
    let μ := (Measure.pi (fun j => multivariateGaussian (0 : State n) (A j))).prod
      (multivariateGaussian (0 : State n) B)
    Integrable (fun x => |root choices factor (f 0) m coordinate x|^(2*p)) μ ∧
      (∫ x, |root choices factor (f 0) m coordinate x|^(2*p) ∂μ) ≤
        constant p choices factor*(scale P choices factor lo hi A0 ν)^(2*p) := by
  intro A B μ
  by_cases hblock : block choices factor = []
  · have hmeas : Measurable (root choices factor (f 0) m coordinate) :=
      jointBlock_measurable choices factor (f 0) hfm _ (by fun_prop) _
    have hb (x : (Fin r → State n) × State n) : |root choices factor (f 0) m coordinate x| ≤ A0 := by
      simpa only [root, jointBlock, blockFunction, hblock, fractionDifferences, List.foldr_nil,
        pow_zero, mul_one] using hfb 0 (Nat.zero_le _) (affineSum (m coordinate+x.2 coordinate)
          (fun _ : Fin r => EuclideanSpace.proj (𝕜 := ℝ) coordinate)
          (suppress (suppressed choices factor) x.1))
    have hpow (x : (Fin r → State n) × State n) :
        |root choices factor (f 0) m coordinate x|^(2*p) ≤ A0^(2*p) :=
      pow_le_pow_left₀ (abs_nonneg _) (hb x) _
    have hi' : Integrable (fun x => |root choices factor (f 0) m coordinate x|^(2*p)) μ :=
      (integrable_const (A0^(2*p))).mono' (by fun_prop) (ae_of_all _ (fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (abs_nonneg _) _)]
        exact hpow x))
    refine ⟨hi', ?_⟩
    have hh := integral_mono hi' (integrable_const (A0^(2*p))) hpow
    simpa [constant, scale, hblock] using hh
  · have hlen : 0 < (block choices factor).length := List.length_pos_iff.mpr hblock
    have hh := PhysicalJointBlocks.root_block_even_moment target target center
      (fun i => (ht i).1) (fun i => (ht i).2.trans P.horizon_le_one) (fun _ => le_rfl) _
      (referenceProfile_measurable P Λ u d)
      (fun q => ⟨(mul_nonneg (fraction_pos P).le P.lower_pos.le).trans (referenceProfile_bounds P Λ u d q).1,
        (referenceProfile_bounds P Λ u d q).2⟩) lo hi hlo hgap hstop B choices hnd factor hlen coordinate
      f hA0 hν hf hfb (fun y => m coordinate+y coordinate) (by fun_prop) p
    simpa only [root, constant, hblock, ite_false, scale] using hh

end SHE.ControlledAssignedRoot
