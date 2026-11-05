module

public import SHEStochastic.VectorMildPathTightness

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
noncomputable section

namespace SHEStochastic.VectorMildPathEnvelope
open MeasureTheory SHE SHE.DyadicApproximation SHE.StoppedFourier
open HeatParameterCover HeatParameterPullback StoppedPathPasting
open scoped NNReal ENNReal
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance : Fact (0 < 2*Real.pi) := ⟨by positivity⟩
local instance : Fact ((2 : ENNReal)≠⊤) := ⟨by simp⟩

/-- The spatial L2 norm of a native remainder is bounded by the
supremum of its actual continuous time-space field. -/
theorem scalar_remainder (Y : C(Parameter,ℝ)) (t : ShortTime) :
    ‖NativeRemainderObservation.remainder Y t‖≤‖Y‖ := by
  rw [NativeRemainderObservation.remainder,LinearIsometry.norm_map]
  have hb : ∀ᵐ x : HeatCircle ∂AddCircle.haarAddCircle,
      ‖PhysicalHeatParameterSection.value 2 Y t x‖≤‖Y‖ :=
    (PhysicalHeatParameterSection.value_ae 2 Y t).mono fun x hx => by rw [hx];exact Y.norm_coe_le_norm _
  simpa [measureUnivNNReal] using Lp.norm_le_of_ae_bound (norm_nonneg Y) hb

variable {n : ℕ}

def remainder (H : ℝ≥0) (hH : 0<H) (Y : Fin n → C(Parameter,ℝ)) (t : Time H) :
    VectorHeat.Physical (d := Fin n) :=
  VectorHeat.coordinates.symm (WithLp.toLp 2 (fun i =>
    NativeRemainderObservation.remainder (Y i) (GlobalHeatParameter.normalized H hH t)))

theorem remainder_norm (H : ℝ≥0) (hH : 0<H) (Y : Fin n → C(Parameter,ℝ)) (t : Time H) :
    ‖remainder H hH Y t‖≤∑ i,‖Y i‖ := by
  rw [remainder,LinearIsometryEquiv.norm_map]
  let v := WithLp.toLp 2 (fun i : Fin n =>
    NativeRemainderObservation.remainder (Y i) (GlobalHeatParameter.normalized H hH t))
  have he : (∑ i : Fin n,PiLp.single 2 i (v i))=v := by
    ext i
    simp [PiLp.single_apply]
  change ‖v‖≤_
  rw [←he]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro i _
  rw [PiLp.norm_single]
  exact scalar_remainder (Y i) _

/-- Exact full-vector decomposition of the existing reconstructed mild
path into the original analytic heat orbit and its native remainder. -/
theorem path_eq (H : ℝ≥0) (hH : 0<H) (u : VectorHeat.Physical (d := Fin n))
    (Y : Fin n → C(Parameter,ℝ)) (t : Time H) :
    VectorMildPathTightness.path H hH u Y t=
      VectorHeat.heat (t.val/NativeHeatObservation.timeScale) u+remainder H hH Y t := by
  apply VectorHeat.coordinates.injective
  apply PiLp.ext
  intro i
  rw [map_add]
  change VectorHeat.coordinates (VectorMildPathTightness.path H hH u Y t) i=
    VectorHeat.coordinates (VectorHeat.heat (t.val/NativeHeatObservation.timeScale) u) i+
      VectorHeat.coordinates (remainder H hH Y t) i
  rw [VectorMildPathTightness.component,VectorHeat.coordinate_heat]
  change _+_=_+VectorHeat.coordinates (VectorHeat.coordinates.symm _) i
  rw [LinearIsometryEquiv.apply_symm_apply]
  rfl

/-- The deterministic bound used for L2 exit control needs only L2
initial data, with no initial supremum norm and no dimension loss in
its heat contribution. -/
theorem norm_bound (H : ℝ≥0) (hH : 0<H) (u : VectorHeat.Physical (d := Fin n))
    (Y : Fin n → C(Parameter,ℝ)) (t : Time H) :
    ‖VectorMildPathTightness.path H hH u Y t‖≤‖u‖+∑ i,‖Y i‖ := by
  rw [path_eq H hH u Y t]
  exact (norm_add_le _ _).trans (add_le_add (VectorHeat.contraction _ u) (remainder_norm H hH Y t))

end SHEStochastic.VectorMildPathEnvelope
