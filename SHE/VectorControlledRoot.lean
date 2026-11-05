module

public import SHE.VectorPhysicalRoot
public import SHE.ControlledAssignedRoot

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
noncomputable section

namespace SHE.VectorControlledRoot
open Set MeasureTheory ProbabilityTheory Real GaussianIncrement GaussianAssignmentBlocks
  GaussianVectorFractions GaussianCoordinates ControlledOldIntervals OldIntervalCovariance
  StoppedGaussianFeatures StoppedFourier ProfileVariance
open scoped BigOperators
local instance : Fact (0 < 2 * π) := ⟨by positivity⟩
variable {n d r k : ℕ}

def value (choices : List (Fin r × Fin k)) (factor : Fin k) (F : State d → ℝ)
    (mean : State n) (g : Fin d → Fin n) : (Fin r → State n) × State n → ℝ :=
  VectorJointRoot.value choices factor F (fun y => projection g (mean+y))
    (fun _ => projection g)

theorem value_measurable (choices : List (Fin r × Fin k)) (factor : Fin k) (F : State d → ℝ)
    (hF : Measurable F) (mean : State n) (g : Fin d → Fin n) :
    Measurable (value choices factor F mean g) :=
  VectorJointRoot.measurable_value choices factor F hF _ (by fun_prop) _

theorem scale_nonneg (P : CanonicalCovariance.ProfileParameters) (choices : List (Fin r × Fin k))
    (factor : Fin k) (lo hi : Fin r → ℝ) (hgap : ∀ j, lo j ≤ hi j)
    {A0 ν : ℝ} (hA0 : 0 ≤ A0) (hν : 0 ≤ ν) (d : ℕ) :
    0 ≤ VectorPhysicalRoot.scale choices factor lo hi A0 ν (P.lower/2) d := by
  unfold VectorPhysicalRoot.scale
  apply mul_nonneg (mul_nonneg (mul_nonneg (by positivity) hA0) (by positivity))
  exact Finset.prod_nonneg (fun j _ => le_min (by norm_num)
    (mul_nonneg (mul_nonneg hν (sqrt_nonneg _)) (rpow_nonneg (sub_nonneg.mpr (hgap _)) _)))

/-- The controlled actual root factor may be any finite smooth cylinder,
including an empty assigned block. Every original old-gap clip remains. -/
theorem root_even_moment (P : CanonicalCovariance.ProfileParameters)
    (Λ : ℝ) (u dir : CircleL2) (θ : ℝ) (lo hi : Fin r → ℝ)
    (σ target : Fin n → ℝ) (center : Fin n → HeatCircle)
    (hσ : ∀ i, 0 < σ i) (hσ1 : ∀ i, σ i ≤ 1) (hages : ∀ i, σ i ≤ target i)
    (hlo : ∀ j, 0 ≤ lo j) (hgap : ∀ j, lo j < hi j)
    (hstop : ∀ j i, σ i ≤ lo j ∨ hi j ≤ σ i)
    (mean : State n) (g : Fin d → Fin n)
    (choices : List (Fin r × Fin k)) (hnd : (choices.map Prod.fst).Nodup) (factor : Fin k)
    (F : State d → ℝ) {A0 ν : ℝ} (hA0 : 0 ≤ A0) (hν : 0 ≤ ν)
    (hF : ContDiff ℝ (block choices factor).length F)
    (hfb : ∀ j, j ≤ (block choices factor).length → ∀ z,
      ‖iteratedFDeriv ℝ j F z‖ ≤ A0*ν^j) (p : ℕ) (hp : 0 < p) :
    let A := familyCovariance σ target center (referenceProfile P Λ u dir) lo hi
    let B := ControlledFixedReserve.covariance P Λ u dir (fixedProfile P Λ u dir lo hi)
      σ target center 0 θ
    let μ := (Measure.pi (fun j => multivariateGaussian (0 : State n) (A j))).prod
      (multivariateGaussian (0 : State n) B)
    Integrable (fun x => |value choices factor F mean g x|^(2*p)) μ ∧
      (∫ x, |value choices factor F mean g x|^(2*p) ∂μ) ≤
        ControlledAssignedRoot.constant p choices factor*
          (VectorPhysicalRoot.scale choices factor lo hi A0 ν (P.lower/2) d)^(2*p) := by
  intro A B μ
  by_cases hblock : block choices factor = []
  · have hb (x : (Fin r → State n) × State n) : |value choices factor F mean g x| ≤ A0 := by
      simpa only [value, VectorJointRoot.value, hblock, fractionDifferences, List.foldr_nil,
        norm_iteratedFDeriv_zero, Real.norm_eq_abs, pow_zero, mul_one] using
        hfb 0 (Nat.zero_le _) (VectorRootClips.affineSum (projection g (mean+x.2))
          (fun _ : Fin r => projection g) (suppress (suppressed choices factor) x.1))
    have hpow (x : (Fin r → State n) × State n) : |value choices factor F mean g x|^(2*p) ≤ A0^(2*p) :=
      pow_le_pow_left₀ (abs_nonneg _) (hb x) _
    have hi' : Integrable (fun x => |value choices factor F mean g x|^(2*p)) μ :=
      (integrable_const (A0^(2*p))).mono' (by
        have hf := value_measurable choices factor F hF.continuous.measurable mean g
        fun_prop) (ae_of_all _ (fun x => by
          rw [Real.norm_eq_abs,abs_of_nonneg (pow_nonneg (abs_nonneg _) _)]
          exact hpow x))
    refine ⟨hi', ?_⟩
    have hh := integral_mono hi' (integrable_const (A0^(2*p))) hpow
    simpa [ControlledAssignedRoot.constant,VectorPhysicalRoot.scale,hblock] using hh
  · have hlen : 0 < (block choices factor).length := List.length_pos_iff.mpr hblock
    have hh := VectorPhysicalRoot.root_even_moment σ target center hσ hσ1 hages _
      (referenceProfile_measurable P Λ u dir)
      (fun q => ⟨(mul_nonneg (fraction_pos P).le P.lower_pos.le).trans (referenceProfile_bounds P Λ u dir q).1,
        (referenceProfile_bounds P Λ u dir q).2⟩) lo hi hlo hgap hstop B choices hnd factor hlen g
      F hA0 hν hF hfb (fun y => projection g (mean+y)) (by fun_prop) p hp
    simpa only [value,ControlledAssignedRoot.constant,hblock,ite_false] using hh

end SHE.VectorControlledRoot
