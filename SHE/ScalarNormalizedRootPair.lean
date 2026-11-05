module

public import SHE.NormalizedScalarMoment
public import SHE.PairedControlledRootMoments

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
noncomputable section

namespace SHE.ScalarNormalizedRootPair
open Set MeasureTheory ProbabilityTheory Real GaussianIncrement GaussianAssignmentBlocks
  GaussianCoordinates StoppedGaussianFeatures StoppedFourier
open scoped BigOperators
local instance scalarNormalizedRootPair_periodPositive : Fact (0<2*π) := ⟨by positivity⟩
variable {n r k : ℕ}

/-- In the scalar case the root current source is exactly one original
observation coordinate; no new vector-root extension is involved. -/
theorem projection_norm (g : Fin 1→Fin n) (z : State n) : ‖projection g z‖=|z (g 0)| := by
  have he : ‖projection g z‖^2=(z (g 0))^2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    simp only [Fin.sum_univ_one,projection_apply]
  nlinarith [norm_nonneg (projection g z),abs_nonneg (z (g 0)),sq_abs (z (g 0))]

/-- Remove the actual scalar current clip before the old/residual
Gaussian expectation, retaining every original old root clip. -/
theorem even_moment (σ target : Fin n→ℝ) (center : Fin n→HeatCircle)
    (hσ : ∀ i,0<σ i) (hσ1 : ∀ i,σ i≤1) (hages : ∀ i,σ i≤target i)
    (c : Domain→ℝ) (hc : Measurable c) {M : ℝ} (hcb : ∀ z,0≤c z ∧ c z≤M)
    (lo hi : Fin r→ℝ) (hlo : ∀ j,0≤lo j) (hgap : ∀ j,lo j<hi j)
    (hstop : ∀ j i,σ i≤lo j ∨ hi j≤σ i) (B : Matrix (Fin n) (Fin n) ℝ)
    (choices : List (Fin r×Fin k)) (hnd : (choices.map Prod.fst).Nodup) (factor : Fin k)
    (g : Fin 1→Fin n) (F : State 1→ℝ) {A0 ν χ : ℝ}
    (hA0 : 0≤A0) (hν : 0≤ν) (hχ0 : 0≤χ) (hχ1 : χ≤1)
    (hF : ContDiff ℝ ((block choices factor).length+1) F)
    (hb : ∀ j,j≤(block choices factor).length+1→∀z,‖iteratedFDeriv ℝ j F z‖≤A0*ν^j)
    (newMean oldMean : State n) (p : ℕ) (hp : 0<p) :
    let A:=OldIntervalCovariance.familyCovariance σ target center c lo hi
    let μ:=(Measure.pi (fun j=>multivariateGaussian (0:State n) (A j))).prod (multivariateGaussian (0:State n) B)
    let source:=(min 1 (ν*‖projection g (newMean-oldMean)‖))^χ
    let N:=fun x=>NormalizedScalarMoment.value
      (VectorControlledRoot.value choices factor F newMean g x-VectorControlledRoot.value choices factor F oldMean g x) source
    Integrable (fun x=>|N x|^(2*p)) μ ∧
      (∫ x,|N x|^(2*p) ∂μ)≤ControlledAssignedRoot.constant p choices factor*
        (2*VectorPhysicalRoot.scale choices factor lo hi A0 ν M 1)^(2*p) := by
  intro A μ source N
  have hh:=PairedControlledRootMoments.even_moment σ target center hσ hσ1 hages c hc hcb
    lo hi hlo hgap hstop B choices hnd factor g F hA0 hν hχ0 hχ1 hF hb newMean oldMean p hp
  dsimp only at hh
  have hs : 0≤source:=rpow_nonneg
    (le_min (by norm_num) (mul_nonneg hν (norm_nonneg _))) _
  have hS : 0≤2*VectorPhysicalRoot.scale choices factor lo hi A0 ν M 1 := by
    unfold VectorPhysicalRoot.scale
    apply mul_nonneg (by norm_num)
    apply mul_nonneg
    · exact mul_nonneg (mul_nonneg (pow_nonneg (by norm_num) _) hA0)
        (pow_nonneg (by norm_num) _)
    · apply Finset.prod_nonneg
      intro j _
      exact le_min (by norm_num) (mul_nonneg (mul_nonneg hν (sqrt_nonneg _))
        (rpow_nonneg (sub_pos.mpr (hgap _)).le _))
  have he : 2*(min 1 (ν*‖projection g (newMean-oldMean)‖))^χ*
      VectorPhysicalRoot.scale choices factor lo hi A0 ν M 1=
      source*(2*VectorPhysicalRoot.scale choices factor lo hi A0 ν M 1) := by dsimp [source];ring
  rw [he] at hh
  exact NormalizedScalarMoment.even_moment μ _ p hp hs
    (ControlledAssignedRoot.constant_nonneg _ _ _) hS hh.1 hh.2

theorem source_bound {ν χ : ℝ} (hν : 0≤ν) (hχ : 0≤χ)
    (g : Fin 1→Fin n) (newMean oldMean : State n) :
    (min 1 (ν*‖projection g (newMean-oldMean)‖))^χ≤ν^χ*|(newMean-oldMean) (g 0)|^χ := by
  have hh:=rpow_le_rpow (le_min (by norm_num) (mul_nonneg hν (norm_nonneg _)))
    (min_le_right (1:ℝ) (ν*‖projection g (newMean-oldMean)‖)) hχ
  rw [mul_rpow hν (norm_nonneg _),projection_norm] at hh
  simpa only [projection_norm] using hh

end SHE.ScalarNormalizedRootPair
