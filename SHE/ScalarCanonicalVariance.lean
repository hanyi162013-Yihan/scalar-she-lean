module

public import SHE.ScalarCovarianceTailScale
public import SHE.ControlledReferenceWindows

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
namespace SHE.ScalarCanonicalVariance
open Set MeasureTheory Real StoppedFourier ControlledProfile ScalarCovarianceTailScale
local instance scalarCanonicalVariance_period : Fact (0<2*π):=⟨by positivity⟩

/-- Uniform true future variance of the ACTUAL canonical scalar
reference, for every past input and every interpolation parameter. -/
theorem bounds (P : CanonicalCovariance.ProfileParameters) (Λ θ v b : ℝ) (hvb : v≤b)
    (p : Inputs) (q : ℝ) (hvq : v≤q) (hqb : q<b) (hage : b-q≤1) (x : HeatCircle) :
    let W:=ControlledReferenceWindows.window P Λ θ v (observation b x) b hvb (fun _=>le_rfl) p
    ProfileVariance.lowerConstant*P.lower*(b-q)^(1/2:ℝ)≤(W.path q).val 0 0 ∧
      (W.path q).val 0 0≤ProfileVariance.upperConstant*P.upper*(b-q)^(1/2:ℝ) := by
  intro W
  rw [W.path_eq ⟨hvq,hqb.le⟩]
  exact elliptic (ControlledReferenceWindows.coefficient_section_measurable P Λ θ v p)
    hqb hage P.lower_pos.le P.upper_nonneg (ControlledReferenceWindows.coefficient_bounds P Λ θ v p) x

theorem positive (P : CanonicalCovariance.ProfileParameters) (Λ θ v b : ℝ) (hvb : v≤b)
    (p : Inputs) (q : ℝ) (hvq : v≤q) (hqb : q<b) (hage : b-q≤1) (x : HeatCircle) :
    let W:=ControlledReferenceWindows.window P Λ θ v (observation b x) b hvb (fun _=>le_rfl) p
    0<(W.path q).val 0 0 := by
  intro W
  exact (mul_pos (mul_pos ProfileVariance.lowerConstant_pos P.lower_pos)
    (Real.rpow_pos_of_pos (sub_pos.mpr hqb) _)).trans_le
      (bounds P Λ θ v b hvb p q hvq hqb hage x).1

end SHE.ScalarCanonicalVariance
