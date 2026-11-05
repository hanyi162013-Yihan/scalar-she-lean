module

public import SHE.NativeHeatObservation
public import SHE.HaarReference
public import SHE.ControlledResidualField

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHE.NativeHaarReferenceEnergy
open Set MeasureTheory StoppedFourier FiniteHaar
local instance : Fact (0 < (1:ℝ)) := ⟨zero_lt_one⟩
local instance : Fact (0 < 2*Real.pi) := ⟨by positivity⟩
local instance : Fact ((2:ENNReal)≠⊤) := ⟨by simp⟩

/-- The actual real Hilbert-column kernel difference has exactly the
native common-Haar reference energy. In particular no pointwise square
root coupling is substituted for the manuscript's nonlocal factor. -/
theorem kernel_difference_energy {ell M t : ℝ} (hell : 0<ell) (ht : 0<t)
    (f g : EllipticField ell M) :
    ‖NativeHeatObservation.kernel ell M hell (t,f)-NativeHeatObservation.kernel ell M hell (t,g)‖^2 =
      HaarReference.nativeEnergy (CircleNormalization.push f.val) (CircleNormalization.push g.val) t := by
  rw [HilbertColumns.norm_sq]
  apply tsum_congr
  intro q
  change ‖NativeHeatObservation.kernel ell M hell (t,f) q-
    NativeHeatObservation.kernel ell M hell (t,g) q‖^2 = _
  rw [←NativeHeatObservation.embed_norm, map_sub,
    NativeHeatObservation.kernel_column hell ht,NativeHeatObservation.kernel_column hell ht]
  rw [HaarReference.nativeColumn_heat _ _ ht.le]
  simp only [LinearIsometryEquiv.symm_apply_apply]
  rw [←map_sub,←map_sub]
  rfl

end SHE.NativeHaarReferenceEnergy
