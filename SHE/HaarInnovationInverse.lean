module

public import SHE.HaarRealSpace

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHE.FiniteHaar
open MeasureTheory CircleHeat DyadicApproximation Filter
open scoped ENNReal NNReal Topology
local instance haarInnovationInverse_local1 : Fact ((2:ENNReal) ≠ ⊤) := ⟨by simp⟩
local instance haarInnovationInverse_local2 : MeasurableSpace CircleL2 := borel CircleL2
local instance haarInnovationInverse_local3 : BorelSpace CircleL2 := ⟨rfl⟩
local instance haarInnovationInverse_local4 : MeasurableSpace RealL2 := borel RealL2
local instance haarInnovationInverse_local5 : BorelSpace RealL2 := ⟨rfl⟩
local instance haarInnovationInverse_local6 : MeasurableSpace RealHaarInput := borel RealHaarInput
local instance haarInnovationInverse_local7 : BorelSpace RealHaarInput := ⟨rfl⟩

theorem continuous_fieldRealInnovationInverse_fixed (ell M : ℝ) (hell : 0 < ell) (v : RealHaarInput) :
    Continuous (fun f : EllipticField ell M => (fieldRealInnovation ell M hell f).symm v) := by
  apply continuous_iff_continuousAt.mpr
  intro f
  change Tendsto (fun g : EllipticField ell M => (fieldRealInnovation ell M hell g).symm v)
    (𝓝 f) (𝓝 ((fieldRealInnovation ell M hell f).symm v))
  rw [tendsto_iff_norm_sub_tendsto_zero]
  let x := (fieldRealInnovation ell M hell f).symm v
  have hp : Continuous (fun g : EllipticField ell M => (g,x)) := continuous_id.prodMk continuous_const
  have hc := (continuous_fieldRealInnovation_joint ell M hell).comp hp
  change Continuous (fun g : EllipticField ell M => fieldRealInnovation ell M hell g x) at hc
  have hr : Tendsto (fun g : EllipticField ell M => v-fieldRealInnovation ell M hell g x)
      (𝓝 f) (𝓝 (v-fieldRealInnovation ell M hell f x)) :=
    tendsto_const_nhds.sub (hc.tendsto f)
  have hz : Tendsto (fun g : EllipticField ell M => v-fieldRealInnovation ell M hell g x)
      (𝓝 f) (𝓝 (0:RealHaarInput)) := by
    simpa only [x,LinearIsometryEquiv.apply_symm_apply,sub_self] using hr
  have he (g : EllipticField ell M) :
      ‖(fieldRealInnovation ell M hell g).symm v-(fieldRealInnovation ell M hell f).symm v‖=
        ‖v-fieldRealInnovation ell M hell g x‖ := by
    rw [← (fieldRealInnovation ell M hell g).norm_map, map_sub,LinearIsometryEquiv.apply_symm_apply]
  simpa only [he,norm_zero] using hz.norm

theorem continuous_fieldRealInnovationInverse_joint (ell M : ℝ) (hell : 0 < ell) :
    Continuous (fun p : EllipticField ell M × RealHaarInput =>
      (fieldRealInnovation ell M hell p.1).symm p.2) := by
  apply continuous_prod_of_continuous_lipschitzWith' _ (1:ℝ≥0)
  · intro f
    exact (fieldRealInnovation ell M hell f).symm.lipschitz
  · exact continuous_fieldRealInnovationInverse_fixed ell M hell

theorem measurable_fieldRealInnovationInverse_joint (ell M : ℝ) (hell : 0 < ell) :
    Measurable (fun p : EllipticField ell M × RealHaarInput =>
      (fieldRealInnovation ell M hell p.1).symm p.2) :=
  (continuous_fieldRealInnovationInverse_joint ell M hell).measurable

end SHE.FiniteHaar
