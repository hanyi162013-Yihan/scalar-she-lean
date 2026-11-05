module

public import SHE.ScalarMeanSpatialMoments
public import SHE.NormalizedHeatMass

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1500000
noncomputable section

namespace SHE.ScalarMeanEnvelope
open Set MeasureTheory StoppedFourier CutoffWordLevel CutoffWordHistories PhysicalParentGeometry
  OrderedHeatForests NormalizedKernelSplit PhysicalScoreChain
local instance scalarMassNormalization_nativePositive : Fact (0 < 2*Real.pi) := ⟨by positivity⟩
variable {R : ReferenceData}
variable (L : CutoffWordLevel.Level R HeatCircle 1)

def massCoefficient (k : ℕ) (W : ℝ) : ℝ :=
  ((1+k:ℕ):ℝ)*(W*(Fintype.card (Choices 1 k):ℝ)*Real.sqrt ((Real.sqrt 2)^k)*NativeHeatSpan.sqrtKernelConstant)

theorem massCoefficient_nonneg (k : ℕ) {W : ℝ} (hW : 0 ≤ W) : 0 ≤ massCoefficient k W := by
  unfold massCoefficient
  exact mul_nonneg (Nat.cast_nonneg _) (mul_nonneg
    (mul_nonneg (mul_nonneg hW (Nat.cast_nonneg _)) (Real.sqrt_nonneg _))
      (NativeHeatSpan.sqrtKernelConstant_pos.le))

theorem massBudget_scalar (A : ℝ)
    (hA : ∀ p,(L.observations.observations p 0).target=A)
    (hx : ∀ p,(L.observations.observations p 0).center=p)
    (k : ℕ) (p : History HeatCircle k) (W r : ℝ) :
    massBudget L k p W r=fun y => massCoefficient k W*(A-r)^(1/4:ℝ)*
      ‖ProfileVariance.heatPhysical (8*(A-r)) (rootParameter k p) y‖ := by
  funext y
  simp only [massBudget,massCoefficient,hA,hx]

/-- The actual scalar parent mass is precisely the normalized positive
heat envelope used in the signed negative-input trace. The identity
retains every deterministic old-gap factor in its amplitude. -/
theorem massBudget_heatEnvelope (A : ℝ)
    (hA : ∀ p,(L.observations.observations p 0).target=A)
    (hx : ∀ p,(L.observations.observations p 0).center=p)
    (k : ℕ) (p : History HeatCircle k) (W D r δ : ℝ)
    (hδ : 0 < δ) (hw : 0 < A-r) (y : HeatCircle) :
    D*massBudget L k p W r y=
      heatEnvelope (D*massCoefficient k W*δ^(1/2:ℝ)) δ (A-r) (y,rootParameter k p) := by
  have hc : δ^(1/2:ℝ)*δ^(-(1/2:ℝ))=1 := by
    rw [←Real.rpow_add hδ]
    norm_num
  rw [massBudget_scalar L A hA hx]
  simp only [heatEnvelope,heatAmplitude]
  rw [ProfileL2.heatPhysical_norm_symm (by positivity : 0 < 8*(A-r)) y (rootParameter k p)]
  calc
    _ = (D*massCoefficient k W)*(A-r)^(1/4:ℝ)*
        ‖ProfileVariance.heatPhysical (8*(A-r)) (rootParameter k p) y‖ := by ring
    _ = _ := by rw [show D*massCoefficient k W*δ^(1/2:ℝ)*δ^(-(1/2:ℝ))=
        D*massCoefficient k W from by rw [mul_assoc,hc,mul_one]]

end SHE.ScalarMeanEnvelope
