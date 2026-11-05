module

public import SHE.ControlledSuppressedLeaf
public import SHE.PhysicalJointBlocks

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
noncomputable section

namespace SHE.ControlledAssignedLeaf
open Set MeasureTheory ProbabilityTheory Real GaussianIncrement GaussianAssignmentBlocks
  GaussianVectorFractions GaussianRoughBlocks GaussianRoughBlockMoments JointGaussianBlocks
  GaussianFractionBaselines GaussianCenteredLeafMoments ControlledOldIntervals OldIntervalCovariance
  StoppedGaussianFeatures StoppedFourier ProfileVariance GaussianAudit
open scoped BigOperators
local instance : Fact (0 < 2 * π) := ⟨by positivity⟩
variable [MeasurableSpace CircleL2] [BorelSpace CircleL2] {n r k : ℕ}

def leaf (choices : List (Fin r × Fin k)) (factor : Fin k)
    (a : ℝ → ℝ) (m : State n) (coordinate : Fin n) (baseline : ℝ)
    (x : (Fin r → State n) × State n) : ℝ :=
  fractionDifferences (block choices factor)
    (fun y => a (affineSum (m coordinate + x.2 coordinate)
      (fun _ => EuclideanSpace.proj (𝕜 := ℝ) coordinate) y) - baseline)
    (suppress (suppressed choices factor) x.1)

omit [MeasurableSpace CircleL2] [BorelSpace CircleL2] in
theorem leaf_measurable (choices : List (Fin r × Fin k)) (factor : Fin k)
    (a : ℝ → ℝ) (ha : Measurable a) (m : State n) (coordinate : Fin n) (baseline : ℝ) :
    Measurable (leaf choices factor a m coordinate baseline) := by
  have hF : Measurable (fun x : (Fin r → State n) × State n =>
      a (affineSum (m coordinate + x.2 coordinate)
        (fun _ : Fin r => EuclideanSpace.proj (𝕜 := ℝ) coordinate) x.1) - baseline) := by
    unfold affineSum
    fun_prop
  exact (measurable_parameterDifferences _ _ hF).comp ((measurable_suppress _).prodMap measurable_id)

omit [MeasurableSpace CircleL2] [BorelSpace CircleL2] in
theorem leaf_nonempty (choices : List (Fin r × Fin k)) (factor : Fin k)
    (hblock : block choices factor ≠ []) (a : ℝ → ℝ) (m : State n)
    (coordinate : Fin n) (baseline : ℝ) :
    leaf choices factor a m coordinate baseline =
      jointBlock choices factor a (fun y => m coordinate + y coordinate)
        (fun _ => EuclideanSpace.proj (𝕜 := ℝ) coordinate) := by
  funext x
  exact congrFun (fractionDifferences_sub_const (block choices factor) hblock _ baseline) _

omit [MeasurableSpace CircleL2] [BorelSpace CircleL2] in
theorem leaf_empty (choices : List (Fin r × Fin k)) (factor : Fin k)
    (hblock : block choices factor = []) (a : ℝ → ℝ) (m : State n)
    (coordinate : Fin n) (baseline : ℝ) (x : (Fin r → State n) × State n) :
    leaf choices factor a m coordinate baseline x =
      a (m coordinate + ((∑ j, suppress (suppressed choices factor) x.1 j) + x.2) coordinate) - baseline := by
  have he : ((∑ j, suppress (suppressed choices factor) x.1 j) + x.2) coordinate =
      (∑ j, suppress (suppressed choices factor) x.1 j coordinate) + x.2 coordinate := by
    change (EuclideanSpace.proj (𝕜 := ℝ) coordinate)
      ((∑ j, suppress (suppressed choices factor) x.1 j) + x.2) = _
    rw [map_add, map_sum]
    rfl
  simp only [leaf, hblock, GaussianVectorFractions.fractionDifferences, List.foldr_nil,
    affineSum, EuclideanSpace.coe_proj, he]
  congr 2
  ring

/-- The actual unassigned leaf keeps the full consistent baseline after
foreign-coordinate suppression, with its genuine full-age moment gain. -/
theorem unassigned_even_moment (P : CanonicalCovariance.ProfileParameters)
    (Λ : ℝ) (u d : CircleL2) (θ : ℝ) (lo hi : Fin r → ℝ)
    (hdisjoint : ∀ j l, j ≠ l → hi j ≤ lo l ∨ hi l ≤ lo j)
    (target : Fin n → ℝ) (center : Fin n → HeatCircle)
    (ht : ∀ i, target i ∈ Ioc 0 P.horizon) (m : State n)
    (hm : ∀ i, m i = ControlledProfile.mean Λ u d (θ,(target i,center i)))
    (choices : List (Fin r × Fin k)) (factor : Fin k) (hblock : block choices factor = [])
    (coordinate : Fin n) (p : ℕ) :
    let A := familyCovariance target target center (referenceProfile P Λ u d) lo hi
    let B := ControlledFixedReserve.covariance P Λ u d (fixedProfile P Λ u d lo hi)
      target target center 0 θ
    let μ := (Measure.pi (fun j => multivariateGaussian (0 : State n) (A j))).prod
      (multivariateGaussian (0 : State n) B)
    let F := leaf choices factor P.coefficient m coordinate
      (ControlledProfile.profile P Λ u d (θ,(target coordinate,center coordinate)))
    Integrable (fun x => |F x|^(2*p)) μ ∧
      (∫ x, |F x|^(2*p) ∂μ) ≤ leafMomentConstant p P.exponent*
        (P.holder*(upperConstant*P.upper)^(P.exponent/2)*(target coordinate)^(P.exponent/4))^(2*p) := by
  intro A B μ F
  have he : F = fun x : (Fin r → State n) × State n =>
      P.coefficient (m coordinate + ((∑ j, suppress (suppressed choices factor) x.1 j) + x.2) coordinate) -
        ControlledProfile.profile P Λ u d (θ,(target coordinate,center coordinate)) := by
    funext x
    exact leaf_empty choices factor hblock _ _ _ _ x
  rw [he]
  exact ControlledSuppressedLeaf.leaf_even_moment P Λ u d θ lo hi hdisjoint target center ht m hm
    (suppressed choices factor) coordinate p

omit [MeasurableSpace CircleL2] [BorelSpace CircleL2] in
/-- A nonempty assigned block kills its original baseline exactly and
retains the selected original physical interval's rough gain. -/
theorem assigned_even_moment (P : CanonicalCovariance.ProfileParameters)
    (Λ : ℝ) (u d : CircleL2) (θ : ℝ) (lo hi : Fin r → ℝ)
    (target : Fin n → ℝ) (center : Fin n → HeatCircle)
    (ht : ∀ i, target i ∈ Ioc 0 P.horizon) (hlo : ∀ j, 0 ≤ lo j) (hgap : ∀ j, lo j < hi j)
    (hstop : ∀ j i, target i ≤ lo j ∨ hi j ≤ target i)
    (m : State n) (choices : List (Fin r × Fin k)) (hnd : (choices.map Prod.fst).Nodup)
    (factor : Fin k) (j : Fin r) (hchosen : j ∈ block choices factor) (coordinate : Fin n) (p : ℕ) :
    let A := familyCovariance target target center (referenceProfile P Λ u d) lo hi
    let B := ControlledFixedReserve.covariance P Λ u d (fixedProfile P Λ u d lo hi)
      target target center 0 θ
    let μ := (Measure.pi (fun l => multivariateGaussian (0 : State n) (A l))).prod
      (multivariateGaussian (0 : State n) B)
    let F := leaf choices factor P.coefficient m coordinate
      (ControlledProfile.profile P Λ u d (θ,(target coordinate,center coordinate)))
    Integrable (fun x => |F x|^(2*p)) μ ∧
      (∫ x, |F x|^(2*p) ∂μ) ≤ gaussianAbsMoment (((2*p : ℕ) : ℝ)*P.exponent)*
        ((2 : ℝ)^((block choices factor).length-1)*P.holder*(upperConstant*(P.lower/2))^(P.exponent/2)*
          (hi j-lo j)^(P.exponent/4))^(2*p) := by
  intro A B μ F
  have hblock : block choices factor ≠ [] := by intro he; simp [he] at hchosen
  rw [show F = jointBlock choices factor P.coefficient (fun y => m coordinate + y coordinate)
      (fun _ => EuclideanSpace.proj (𝕜 := ℝ) coordinate) from leaf_nonempty choices factor hblock _ _ _ _]
  apply PhysicalJointBlocks.rough_block_even_moment target target center (fun i => (ht i).1)
    (fun i => (ht i).2.trans P.horizon_le_one) (fun _ => le_rfl) _
    (referenceProfile_measurable P Λ u d)
    (fun q => ⟨(mul_nonneg (fraction_pos P).le P.lower_pos.le).trans (referenceProfile_bounds P Λ u d q).1,
      (referenceProfile_bounds P Λ u d q).2⟩) lo hi hlo hgap hstop B choices hnd factor j hchosen coordinate
    P.coefficient P.measurable P.holder_nonneg P.exponent_pos.le P.holder_bound _ (by fun_prop) p

end SHE.ControlledAssignedLeaf
