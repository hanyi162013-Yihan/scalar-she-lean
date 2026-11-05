module

public import SHE.JointInterpolationAlgebra
public import SHE.VariableObservations

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1600000
noncomputable section

namespace SHE.NativeHeatObservation
open Set MeasureTheory Real AddCircle StoppedFourier DyadicApproximation
local instance jointInterpolationFields_periodPos : Fact (0<2*π) := ⟨by positivity⟩
local instance jointInterpolationFields_realMeasurable : MeasurableSpace RealL2 := borel _
local instance jointInterpolationFields_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance jointInterpolationFields_nativeMeasurable : MeasurableSpace CircleL2 := borel _
local instance jointInterpolationFields_nativeBorel : BorelSpace CircleL2 := ⟨rfl⟩

/-- Genuine joint Borel dependence of the native heat observation,
including its prescribed zero extension at nonpositive ages. -/
theorem functional_joint_measurable :
    Measurable (fun z : RealL2×(ℝ×HeatCircle)=>functional z.2.1 z.2.2 z.1) := by
  classical
  have hm := PhysicalProfile.physicalHeatMean_joint_measurable.comp
    ((embed.continuous.measurable.comp measurable_fst).prodMk measurable_snd)
  have hset : MeasurableSet {z : RealL2×(ℝ×HeatCircle) | 0<z.2.1} :=
    measurableSet_lt measurable_const measurable_snd.fst
  convert! hm.ite hset (measurable_const (a:=(0:ℝ))) using 1
  funext z
  by_cases ht : 0<z.2.1
  · simp only [ite_eq_left ht,functional_physical ht,Function.comp_apply]
  · simp only [ite_eq_right ht,functional_apply,circleHeat,dite_eq_right ht,inner_zero_left,Complex.zero_re]
  all_goals infer_instance

end SHE.NativeHeatObservation

namespace SHE.JointInterpolationAlgebra
open Set MeasureTheory Real StoppedFourier NativeHeatObservation DyadicApproximation
local instance jointInterpolationCurrent_realMeasurable : MeasurableSpace RealL2 := borel _
local instance jointInterpolationCurrent_realBorel : BorelSpace RealL2 := ⟨rfl⟩
variable {W X : Type*} [MeasurableSpace W] [MeasurableSpace X] {n : ℕ}

/-- Every original observation and both current states may depend on
the outer parameters. The actual joint interpolation is Borel before
spatial/history Fubini, with each original stop in its own damper. -/
theorem current_variable_measurable (Z : VariableObservations.Family X n)
    (Λ q θ : ℝ) (U V : W→RealL2) (hU : Measurable U) (hV : Measurable V) :
    Measurable (fun z : W×X=>current Λ q θ (U z.1) (V z.1) (Z.observations z.2)) := by
  apply (WithLp.measurable_toLp 2 (Fin n→ℝ)).comp
  apply Measurable.of_eval
  intro i
  have hT := (Z.target_measurable i).comp (measurable_snd : Measurable (Prod.snd : W×X→X))
  have hx := (Z.center_measurable i).comp (measurable_snd : Measurable (Prod.snd : W×X→X))
  have hs := (Z.stop_measurable i).comp (measurable_snd : Measurable (Prod.snd : W×X→X))
  have harg := (hT.sub_const q).prodMk hx
  have hu := functional_joint_measurable.comp ((hU.comp measurable_fst).prodMk harg)
  have hv := functional_joint_measurable.comp ((hV.comp measurable_fst).prodMk harg)
  simp_rw [map_sub]
  exact hu.add ((((hs.sub_const q).const_mul (-Λ)).exp.const_mul θ).mul (hv.sub hu))

end SHE.JointInterpolationAlgebra
