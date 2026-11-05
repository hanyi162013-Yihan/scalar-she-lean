module

public import SHEStochastic.GlobalHeatPathTightness
public import SHEStochastic.VectorHeat
public import SHEStochastic.TightnessFromCompactControl
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
noncomputable section

namespace SHEStochastic.VectorMildPathTightness
open MeasureTheory SHE SHE.DyadicApproximation StoppedPathPasting HeatParameterCover
open scoped NNReal ENNReal
local instance : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨by simp⟩
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance : Fact (0 < 2*Real.pi) := ⟨by positivity⟩
variable {d : Type*} [Fintype d] [DecidableEq d]
local instance : SecondCountableTopology (VectorHeat.Physical (d := d)) := Lp.SecondCountableTopology
local instance : MeasurableSpace (VectorHeat.Physical (d := d)) := borel _
local instance : BorelSpace (VectorHeat.Physical (d := d)) := ⟨rfl⟩
local instance : MeasurableSpace RealL2 := borel _
local instance : BorelSpace RealL2 := ⟨rfl⟩

/-- Reconstruct the actual vector L2 path through the existing isometry
between vector L2 and its finite Hilbert sum of scalar components. -/
def assemble (H : ℝ≥0) (W : d → Path H RealL2) : Path H (VectorHeat.Physical (d := d)) :=
  ⟨fun t => VectorHeat.coordinates.symm (WithLp.toLp 2 (fun i => W i t)),
    (VectorHeat.coordinates (d := d)).symm.continuous.comp
      ((PiLp.continuous_toLp 2 (fun _ : d => RealL2)).comp (continuous_pi fun i => (W i).continuous))⟩

theorem continuous_assemble (H : ℝ≥0) : Continuous (assemble (d := d) H) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  have hi (i : d) : Continuous (fun z : (d → Path H RealL2) × Time H => z.1 i z.2) :=
    continuous_eval.comp (((continuous_apply i).comp continuous_fst).prodMk continuous_snd)
  exact (VectorHeat.coordinates (d := d)).symm.continuous.comp
    ((PiLp.continuous_toLp 2 (fun _ : d => RealL2)).comp (continuous_pi hi))

/-- The scalar native mild-path map is reused once in each coordinate. -/
def path (H : ℝ≥0) (hH : 0 < H) (u : VectorHeat.Physical (d := d))
    (Y : d → C(Parameter,ℝ)) : Path H (VectorHeat.Physical (d := d)) :=
  assemble H (fun i => GlobalHeatPathTightness.path H hH (VectorHeat.coordinates u i) (Y i))

theorem component (H : ℝ≥0) (hH : 0 < H) (u : VectorHeat.Physical (d := d))
    (Y : d → C(Parameter,ℝ)) (t : Time H) (i : d) :
    VectorHeat.coordinates (path H hH u Y t) i =
      NativeHeatObservation.heat t.val (VectorHeat.coordinates u i)+
        NativeRemainderObservation.remainder (Y i) (GlobalHeatParameter.normalized H hH t) := by
  change VectorHeat.coordinates (VectorHeat.coordinates.symm (WithLp.toLp 2
    (fun i => GlobalHeatPathTightness.path H hH (VectorHeat.coordinates u i) (Y i) t))) i = _
  rw [LinearIsometryEquiv.apply_symm_apply]
  rfl

theorem continuous_joint (H : ℝ≥0) (hH : 0 < H) :
    Continuous (fun z : VectorHeat.Physical (d := d) × (d → C(Parameter,ℝ)) => path H hH z.1 z.2) := by
  have hi (i : d) : Continuous (fun z : VectorHeat.Physical (d := d) × (d → C(Parameter,ℝ)) =>
      GlobalHeatPathTightness.path H hH (VectorHeat.coordinates z.1 i) (z.2 i)) := by
    have hc : Continuous (fun u : VectorHeat.Physical (d := d) => VectorHeat.coordinates u i) :=
      (PiLp.proj (𝕜 := ℝ) 2 (fun _ : d => RealL2) i).continuous.comp
        (VectorHeat.coordinates (d := d)).continuous
    have hp : Continuous (fun z : VectorHeat.Physical (d := d) × (d → C(Parameter,ℝ)) =>
        (VectorHeat.coordinates z.1 i,z.2 i)) :=
      (hc.comp continuous_fst).prodMk ((continuous_apply i).comp continuous_snd)
    exact Continuous.comp
      (g := fun p : RealL2 × C(Parameter,ℝ) => GlobalHeatPathTightness.path H hH p.1 p.2)
      (f := fun z : VectorHeat.Physical (d := d) × (d → C(Parameter,ℝ)) =>
        (VectorHeat.coordinates z.1 i,z.2 i))
      (MildPathTightness.continuous_joint H (GlobalHeatPathTightness.timeMap H hH)) hp
  exact (continuous_assemble H).comp (continuous_pi hi)

/-- Tight full coupled point-field laws give tight vector state paths
with a fixed random initial law, even when the initial state and noise
are dependent. No pointwise bound on the initial state is required. -/
theorem tight_random_initial {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Z : Ω → VectorHeat.Physical (d := d)) (hZ : Measurable Z)
    (Y : ℕ → Ω → (d → C(Parameter,ℝ))) (hY : ∀ m, Measurable (Y m))
    (htight : IsTightMeasureSet (Set.range (fun m => μ.map (Y m)))) (H : ℝ≥0) (hH : 0 < H) :
    IsTightMeasureSet (Set.range (fun m => μ.map (fun ω => path H hH (Z ω) (Y m ω)))) := by
  have hz : IsTightMeasureSet (Set.range (fun _ : ℕ => μ.map Z)) := by
    simpa only [Set.range_const] using (isTightMeasureSet_singleton (μ := μ.map Z))
  have hp := TightnessFromCompactControl.paired μ (fun _ : ℕ => Z) Y (fun _ => hZ) hY hz htight
  have ht := hp.map (continuous_joint H hH)
  have he : Measure.map (fun z : VectorHeat.Physical (d := d) × (d → C(Parameter,ℝ)) => path H hH z.1 z.2) ''
      Set.range (fun m => μ.map (fun ω => (Z ω,Y m ω))) =
      Set.range (fun m => μ.map (fun ω => path H hH (Z ω) (Y m ω))) := by
    rw [← Set.range_comp']
    congr 1
    funext m
    exact Measure.map_map (continuous_joint H hH).measurable (hZ.prodMk (hY m))
  rwa [he] at ht

end SHEStochastic.VectorMildPathTightness
