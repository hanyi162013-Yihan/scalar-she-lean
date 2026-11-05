module

public import SHEStochastic.NativeRemainderObservation
public import SHEStochastic.BoundedHeatTightness
public import SHEStochastic.StoppedPathPasting

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
noncomputable section

namespace SHEStochastic.MildPathTightness
open MeasureTheory SHE SHE.StoppedFourier SHE.DyadicApproximation SHE.FiniteHaar AddCircle
open HeatParameterCover HeatParameterPullback StoppedPathPasting
open scoped ENNReal NNReal

local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance : SecondCountableTopology CircleHeat.CircleL2 :=
  (_root_.fourierBasis (T := (1 : ℝ))).repr.toHomeomorph.secondCountableTopology
local instance : SecondCountableTopology RealL2 := realCircleIdentification.toHomeomorph.secondCountableTopology
local instance : MeasurableSpace RealL2 := borel _
local instance : BorelSpace RealL2 := ⟨rfl⟩

/-- The original native L2 state path, obtained from a continuous
physical remainder and the deterministic heat flow of L2 initial data. -/
def path (H : ℝ≥0) (j : C(Time H, ShortTime)) (u₀ : RealL2) (Y : C(Parameter, ℝ)) : Path H RealL2 :=
  ⟨fun t ↦ NativeHeatObservation.heat t.val u₀ + NativeRemainderObservation.remainder Y (j t),
    (RealHeat.continuous_realHeat_action.comp
      ((continuous_subtype_val.div_const NativeHeatObservation.timeScale).prodMk continuous_const)).add
        ((NativeRemainderObservation.continuous_remainder Y).comp (j).continuous)⟩

/-- Passing from the compact parameter field to the actual state path
is a contraction. No extra regularity of the initial L2 data is needed. -/
theorem lipschitz (H : ℝ≥0) (j : C(Time H, ShortTime)) (u₀ : RealL2) :
    LipschitzWith 1 (path H j u₀) := by
  apply LipschitzWith.of_dist_le_mul
  intro Y Z
  simp only [NNReal.coe_one, one_mul, dist_eq_norm]
  apply ((path H j u₀ Y - path H j u₀ Z).norm_le (norm_nonneg (Y - Z))).mpr
  intro t
  have he : (path H j u₀ Y - path H j u₀ Z) t =
      NativePhysicalState.pull (PhysicalHeatParameterSection.value 2 Y (j t) -
        PhysicalHeatParameterSection.value 2 Z (j t)) := by
    rw [map_sub]
    change (_ + NativePhysicalState.pull _) - (_ + NativePhysicalState.pull _) = _
    abel
  rw [he, LinearIsometry.norm_map]
  exact PhysicalHeatParameterSection.difference_bound_profiles 2 Y Z _ _ (norm_nonneg _)
    (fun a ↦ (Y - Z).norm_coe_le_norm _)

theorem lipschitz_initial (H : ℝ≥0) (j : C(Time H, ShortTime)) (Y : C(Parameter, ℝ)) :
    LipschitzWith 1 (fun u₀ ↦ path H j u₀ Y) := by
  apply LipschitzWith.of_dist_le_mul
  intro u v
  simp only [NNReal.coe_one, one_mul, dist_eq_norm]
  apply ((path H j u Y - path H j v Y).norm_le (norm_nonneg (u - v))).mpr
  intro t
  have he : (path H j u Y - path H j v Y) t = NativeHeatObservation.heat t.val (u - v) := by
    rw [map_sub]
    change (NativeHeatObservation.heat t.val u + NativeRemainderObservation.remainder Y (j t)) -
      (NativeHeatObservation.heat t.val v + NativeRemainderObservation.remainder Y (j t)) =
        NativeHeatObservation.heat t.val u - NativeHeatObservation.heat t.val v
    abel
  rw [he]
  exact RealHeat.realHeat_contraction _ _

theorem continuous_joint (H : ℝ≥0) (j : C(Time H, ShortTime)) :
    Continuous (fun z : RealL2 × C(Parameter, ℝ) ↦ path H j z.1 z.2) :=
  (LipschitzWith.uncurry (lipschitz_initial H j) (lipschitz H j)).continuous

/-- Uniform tightness of the native convolution fields transfers to
the complete mild state paths by the same proved contraction. -/
theorem tight {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (Y : ℕ → Ω → C(Parameter, ℝ)) (hY : ∀ k, Measurable (Y k))
    (htight : IsTightMeasureSet (Set.range (fun k ↦ μ.map (Y k))))
    (H : ℝ≥0) (j : C(Time H, ShortTime)) (u₀ : RealL2) :
    IsTightMeasureSet (Set.range (fun k ↦ μ.map (fun sample ↦ path H j u₀ (Y k sample)))) := by
  have hh := htight.map (lipschitz H j u₀).continuous
  have he : Measure.map (path H j u₀) '' (Set.range (fun k ↦ μ.map (Y k))) =
      Set.range (fun k ↦ μ.map (fun sample ↦ path H j u₀ (Y k sample))) := by
    rw [← Set.range_comp']
    congr 1
    funext k
    exact Measure.map_map (lipschitz H j u₀).continuous.measurable (hY k)
  rwa [he] at hh

/-- A fixed random initial law also gives tight mild-path laws. The
initial state and convolution may be dependent; tightness of the two
marginals and joint continuity are sufficient. -/
theorem tight_random_initial {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Z : Ω → RealL2) (hZ : Measurable Z)
    (Y : ℕ → Ω → C(Parameter, ℝ)) (hY : ∀ k, Measurable (Y k))
    (htight : IsTightMeasureSet (Set.range (fun k ↦ μ.map (Y k))))
    (H : ℝ≥0) (j : C(Time H, ShortTime)) :
    IsTightMeasureSet (Set.range (fun k ↦ μ.map (fun sample ↦ path H j (Z sample) (Y k sample)))) := by
  let Q (k : ℕ) := μ.map (fun sample ↦ (Z sample, Y k sample))
  have hfst (k : ℕ) : (Q k).fst = μ.map Z := Measure.fst_map_prodMk hZ (hY k)
  have hsnd (k : ℕ) : (Q k).snd = μ.map (Y k) := Measure.snd_map_prodMk hZ (hY k)
  have hf : IsTightMeasureSet (Measure.fst '' Set.range Q) := by
    have he : Measure.fst '' Set.range Q = {μ.map Z} := by
      rw [← Set.range_comp']
      simp only [hfst, Set.range_const]
    rw [he]
    exact isTightMeasureSet_singleton
  have hs : IsTightMeasureSet (Measure.snd '' Set.range Q) := by
    have he : Measure.snd '' Set.range Q = Set.range (fun k ↦ μ.map (Y k)) := by
      rw [← Set.range_comp']
      simp only [hsnd]
    rwa [he]
  have hh := (IsTightMeasureSet.prodMk hf hs).map (continuous_joint H j)
  have he : Measure.map (fun z : RealL2 × C(Parameter, ℝ) ↦ path H j z.1 z.2) '' Set.range Q =
      Set.range (fun k ↦ μ.map (fun sample ↦ path H j (Z sample) (Y k sample))) := by
    rw [← Set.range_comp']
    congr 1
    funext k
    exact Measure.map_map (continuous_joint H j).measurable (hZ.prodMk (hY k))
  rwa [he] at hh

end SHEStochastic.MildPathTightness
