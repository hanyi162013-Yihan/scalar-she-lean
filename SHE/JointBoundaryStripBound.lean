module

public import SHE.JointCutoffBoundary

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section

namespace SHE.JointBoundaryStripBound
open Set MeasureTheory StoppedFourier WordRecursion CutoffWordLevel
open JointWordAnalytic JointCutoffBoundary PhysicalRemainderMass CovarianceEndpoint
local instance jointBoundaryStripBound_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
variable {P Ω : Type*} [MeasurableSpace P] [MeasurableSpace Ω]
variable [MeasurableSpace CircleL2] [BorelSpace CircleL2]
variable {R : ReferenceData} {n : ℕ} (L : Level R P n) (Λ : ℝ)
variable (U V : Ω×ℝ→CircleL2) (XU XV : Ω×(ℝ×HeatCircle)→ℝ)

/-- Actual old joint states may have arbitrary individual stopping
ages. The terminal-strip mass uses only the heat-square singularity. -/
theorem strip_bound {A B C D δ : ℝ} (hA : 0≤A) (ha : ∀ z,|R.totalVariance z|≤A)
    (hB : 0≤B) (hδ : 0≤δ) (p : P) (ω : Ω)
    (hC : ∀ z,‖L.test p z‖≤C) (hD : ∀ z,‖fderiv ℝ (L.test p) z‖≤D)
    (hDD : ∀ z,‖GaussianTaylor.hessian (L.test p) z‖≤B) :
    ‖strip (U := U) (V := V) (XU := XU) (XV := XV) L Λ δ p ω‖≤
      ((1/2:ℝ)*(A+R.upper)*B*n)*heatMass δ := by
  let q := max R.base (L.terminal p-δ)
  let K : ℝ := (1/2:ℝ)*(A+R.upper)*B*n
  have hK : 0≤K := mul_nonneg
    (mul_nonneg (mul_nonneg (by norm_num) (add_nonneg hA R.upper_nonneg)) hB) (Nat.cast_nonneg _)
  have hq : q≤L.terminal p := max_le (L.terminal_base p) (by linarith)
  have hleft : R.base≤q := le_max_left _ _
  have hlen : 0≤L.terminal p-q := sub_nonneg.mpr hq
  have hlenδ : L.terminal p-q≤δ := by dsimp [q]; linarith [le_max_right R.base (L.terminal p-δ)]
  have he : ‖strip (U := U) (V := V) (XU := XU) (XV := XV) L Λ δ p ω‖≤
      ∫ t in q..L.terminal p,K*(1+heatConstant*(L.terminal p-t)^(-(1/2:ℝ))) := by
    unfold strip
    apply intervalIntegral.norm_integral_le_of_norm_le hq ?_ (endpoint_majorant_integrable K)
    filter_upwards [volume.ae_ne (L.terminal p)] with t hne ht
    have hW : t∈Ioo (L.window p).left (L.window p).right := ⟨hleft.trans_lt ht.1,lt_of_le_of_ne ht.2 hne⟩
    exact JointInsertionBounds.spatial_bound (L.window p) hA ha hB (fun tx => XV (ω,tx)) hW
      (GaussianItoTest.backward (L.window p) (L.test p) t) (state L Λ U V XU XV p ω t)
      (BackwardRegularity.gaussian_state_hessian_bound _ ((L.test_uniform.smooth p).of_le (by simp)) hC hD hDD _)
  calc
    _ ≤ ∫ t in q..L.terminal p,K*(1+heatConstant*(L.terminal p-t)^(-(1/2:ℝ))) := he
    _ = K*heatMass (L.terminal p-q) := by
      rw [intervalIntegral.integral_const_mul,heat_majorant_mass hq]
      rfl
    _ ≤ K*heatMass δ := mul_le_mul_of_nonneg_left (heatMass_mono hlen hlenδ) hK

end SHE.JointBoundaryStripBound
