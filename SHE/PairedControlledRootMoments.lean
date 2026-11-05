module

public import SHE.VectorPhysicalPairedRoot
public import SHE.VectorControlledRoot

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1900000
noncomputable section

namespace SHE.PairedControlledRootMoments
open Set MeasureTheory ProbabilityTheory Real GaussianIncrement GaussianAudit GaussianVectorFractions
  GaussianAssignmentBlocks GaussianRoughBlocks GaussianClipMoments GaussianCoordinates
  OldIntervalCovariance OldIntervalVariance StoppedGaussianFeatures StoppedFourier ProfileVariance
open scoped BigOperators NNReal
local instance pairedControlledRootMoments_periodPositive : Fact (0<2*π) := ⟨by positivity⟩
variable {n d r k : ℕ}

theorem difference_eq (choices : List (Fin r×Fin k)) (factor : Fin k)
    (F : State d→ℝ) (newMean oldMean : State n) (g : Fin d→Fin n) :
    (fun x=>VectorControlledRoot.value choices factor F newMean g x-
      VectorControlledRoot.value choices factor F oldMean g x)=
      VectorPairedJointRoot.value choices factor F (fun y=>projection g (oldMean+y))
        (fun _ : Fin r=>projection g) (projection g (newMean-oldMean)) := by
  unfold VectorControlledRoot.value VectorPairedJointRoot.value
  have hm : (fun y : State n=>projection g (oldMean+y)+projection g (newMean-oldMean))=
      (fun y : State n=>projection g (newMean+y)) := by
    funext y
    rw [←map_add]
    congr 1
    abel
  rw [hm]

/-- The actual controlled root at BOTH endpoint means keeps every
original old clip, including the empty root block. The current clip is
explicit and never averaged independently of the old word. -/
theorem even_moment (σ target : Fin n→ℝ) (center : Fin n→HeatCircle)
    (hσ : ∀ i,0<σ i) (hσ1 : ∀ i,σ i≤1) (hages : ∀ i,σ i≤target i)
    (c : Domain→ℝ) (hc : Measurable c) {M : ℝ} (hcb : ∀ z,0≤c z ∧ c z≤M)
    (lo hi : Fin r→ℝ) (hlo : ∀ j,0≤lo j) (hgap : ∀ j,lo j<hi j)
    (hstop : ∀ j i,σ i≤lo j ∨ hi j≤σ i) (B : Matrix (Fin n) (Fin n) ℝ)
    (choices : List (Fin r×Fin k)) (hnd : (choices.map Prod.fst).Nodup) (factor : Fin k)
    (g : Fin d→Fin n) (F : State d→ℝ) {A0 ν χ : ℝ}
    (hA0 : 0≤A0) (hν : 0≤ν) (hχ0 : 0≤χ) (hχ1 : χ≤1)
    (hF : ContDiff ℝ ((block choices factor).length+1) F)
    (hb : ∀ j,j≤(block choices factor).length+1→∀z,‖iteratedFDeriv ℝ j F z‖≤A0*ν^j)
    (newMean oldMean : State n) (p : ℕ) (hp : 0<p) :
    let A:=familyCovariance σ target center c lo hi
    let μ:=(Measure.pi (fun j=>multivariateGaussian (0:State n) (A j))).prod (multivariateGaussian (0:State n) B)
    let G:=fun x=>VectorControlledRoot.value choices factor F newMean g x-
      VectorControlledRoot.value choices factor F oldMean g x
    Integrable (fun x=>|G x|^(2*p)) μ ∧
      (∫ x,|G x|^(2*p) ∂μ)≤ControlledAssignedRoot.constant p choices factor*
        (2*(min 1 (ν*‖projection g (newMean-oldMean)‖))^χ*
          VectorPhysicalRoot.scale choices factor lo hi A0 ν M d)^(2*p) := by
  intro A μ G
  have he:=difference_eq choices factor F newMean oldMean g
  have hgm : Measurable G :=
    (VectorControlledRoot.value_measurable choices factor F hF.continuous.measurable newMean g).sub
      (VectorControlledRoot.value_measurable choices factor F hF.continuous.measurable oldMean g)
  by_cases hblock : block choices factor=[]
  · let C:=2*(min 1 (ν*‖projection g (newMean-oldMean)‖))^χ*A0
    have hC : 0≤C:=by dsimp [C];positivity
    have hpoint (x : (Fin r→State n)×State n) : |G x|≤C := by
      have hh:=VectorPairedJointRoot.pointwise_bound choices hnd factor F hA0 hν hχ0 hχ1 hF hb
        (fun y=>projection g (oldMean+y)) (fun _ : Fin r=>projection g)
        (projection g (newMean-oldMean)) x
      rw [←he] at hh
      simp only [hblock,List.length_nil,zero_add,pow_one,List.map_nil,
        VectorFiniteDifferences.clips,List.prod_nil,mul_one] at hh
      convert! hh using 1
      dsimp [G,C]
      ring
    have hi : Integrable (fun x=>|G x|^(2*p)) μ :=
      (integrable_const (C^(2*p))).mono'
        ((continuous_abs.measurable.comp hgm).pow_const _).aestronglyMeasurable
        (ae_of_all _ (fun x=>by
          rw [Real.norm_of_nonneg (pow_nonneg (abs_nonneg _) _)]
          exact pow_le_pow_left₀ (abs_nonneg _) (hpoint x) _))
    refine ⟨hi,?_⟩
    have hh:=integral_mono hi (integrable_const (C^(2*p)))
      (fun x=>pow_le_pow_left₀ (abs_nonneg _) (hpoint x) (2*p))
    simpa [ControlledAssignedRoot.constant,VectorPhysicalRoot.scale,hblock,C] using hh
  · have hlen : 0<(block choices factor).length:=List.length_pos_iff.mpr hblock
    have hh:=VectorPhysicalPairedRoot.root_even_moment σ target center hσ hσ1 hages c hc hcb
      lo hi hlo hgap hstop B choices hnd factor hlen g F hA0 hν hχ0 hχ1 hF hb
      (fun y=>projection g (oldMean+y)) (by fun_prop) (projection g (newMean-oldMean)) p hp
    dsimp only at hh
    rw [←he] at hh
    simpa only [ControlledAssignedRoot.constant,hblock,ite_false,
      VectorPhysicalPairedRoot.scale,VectorPhysicalRoot.scale] using hh

end SHE.PairedControlledRootMoments
