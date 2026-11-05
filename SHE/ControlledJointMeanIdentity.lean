module

public import SHE.ControlledJointWeightedWord
public import SHE.JointWordObserve
public import SHE.PhysicalMeanSemigroup

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
noncomputable section

namespace SHE.ControlledJointWeightedWord
open Set MeasureTheory StoppedFourier StoppedGaussianScore PhysicalProfile PhysicalMeanRange
  PhysicalMeanSemigroup WordRecursion
open scoped InnerProductSpace
local instance controlledJointMeanIdentity_periodPos : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
variable {n : ℕ}

theorem heatMean_sub {r : ℝ} (hr : 0 < r) (U V : CircleL2) (x : HeatCircle) :
    physicalHeatMean (V-U) (r,x)=physicalHeatMean V (r,x)-physicalHeatMean U (r,x) := by
  simp only [heatMean_eq_real_inner hr,inner_sub_right]

/-- The affine path used in the controlled-profile FTC ends at the
literal stopped joint observation. Each original stop keeps its own
damping and each target keeps its own positive heat age. -/
theorem jointMeanVector_one_eq_evaluate (Λ q : ℝ)
    (U V : ℝ → CircleL2) (XU XV : ℝ × HeatCircle → ℝ)
    (Z : Fin n → Observation) (hages : ∀ i,q < (Z i).target)
    (center : Fin n → UnitAddCircle)
    (hcenter : ∀ i,nativeCenter center i=(Z i).center) :
    jointMeanVector (fun i => (Z i).stop) (fun i => (Z i).target) center q Λ
      (U q) (V q-U q) 1=JointWordObserve.evaluate Λ U V XU XV Z q := by
  apply PiLp.ext
  intro i
  rw [jointMeanVector_apply,heatMean_sub (sub_pos.mpr (hages i)),hcenter i]
  simp only [one_mul,JointWordObserve.evaluate,WithLp.ofLp_toLp,observe,ite_eq_left (hages i)]

theorem jointMeanVector_zero (σ target : Fin n → ℝ) (center : Fin n → UnitAddCircle)
    (q Λ : ℝ) (Z D : CircleL2) :
    jointMeanVector σ target center q Λ Z D 0=currentDirection target center q Z := by
  simp only [jointMeanVector,zero_smul,add_zero]

/-- The entire mean path, rather than just its endpoints, is the
convex interpolation of the actual two endpoint joint means. -/
theorem jointMeanVector_affine_endpoints (σ target : Fin n → ℝ)
    (center : Fin n → UnitAddCircle) (q Λ : ℝ) (Z D : CircleL2) (θ : ℝ) :
    jointMeanVector σ target center q Λ Z D θ=
      (1-θ) • jointMeanVector σ target center q Λ Z D 0+
        θ • jointMeanVector σ target center q Λ Z D 1 := by
  simp only [jointMeanVector,zero_smul,one_smul,add_zero]
  module

/-- Centering at the full controlled profile mean retains the same
affine endpoint identity; no selected leaf baseline is suppressed. -/
theorem centered_jointMeanVector_affine (σ target : Fin n → ℝ)
    (center : Fin n → UnitAddCircle) (q Λ : ℝ) (Z D u d : CircleL2) (θ : ℝ) :
    jointMeanVector σ target center q Λ Z D θ-
        WithLp.toLp 2 (fun i => ControlledProfile.mean Λ u d (θ,(target i,nativeCenter center i)))=
      (1-θ) • (jointMeanVector σ target center q Λ Z D 0-
        WithLp.toLp 2 (fun i => ControlledProfile.mean Λ u d (0,(target i,nativeCenter center i))))+
      θ • (jointMeanVector σ target center q Λ Z D 1-
        WithLp.toLp 2 (fun i => ControlledProfile.mean Λ u d (1,(target i,nativeCenter center i)))) := by
  apply PiLp.ext
  intro i
  simp only [jointMeanVector_apply,ControlledProfile.mean,PiLp.sub_apply,PiLp.add_apply,
    PiLp.smul_apply,WithLp.ofLp_toLp,smul_eq_mul]
  ring

end SHE.ControlledJointWeightedWord
