module

public import SHE.MeanInputFields
public import SHE.ActualInterpolatedMeanFields

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHE.JointInterpolationAlgebra
open Set MeasureTheory Real StoppedFourier NativeHeatObservation DyadicApproximation
local instance meanInputTimeFields_realSigma1 : MeasurableSpace RealL2 := borel _
local instance meanInputTimeFields_realBorel1 : BorelSpace RealL2 := ⟨rfl⟩
variable {W X : Type*} [MeasurableSpace W] [MeasurableSpace X] {n : ℕ}

theorem current_variable_time_measurable (Z : VariableObservations.Family X n)
    (Λ θ : ℝ) (q : W→ℝ) (hq : Measurable q)
    (U V : W→RealL2) (hU : Measurable U) (hV : Measurable V) :
    Measurable (fun z : W×X=>current Λ (q z.1) θ (U z.1) (V z.1) (Z.observations z.2)) := by
  apply (WithLp.measurable_toLp 2 (Fin n→ℝ)).comp
  apply Measurable.of_eval
  intro i
  have hT := (Z.target_measurable i).comp (measurable_snd : Measurable (Prod.snd : W×X→X))
  have hx := (Z.center_measurable i).comp (measurable_snd : Measurable (Prod.snd : W×X→X))
  have hs := (Z.stop_measurable i).comp (measurable_snd : Measurable (Prod.snd : W×X→X))
  have hQ := hq.comp (measurable_fst : Measurable (Prod.fst : W×X→W))
  have harg := (hT.sub hQ).prodMk hx
  have hu := functional_joint_measurable.comp ((hU.comp measurable_fst).prodMk harg)
  have hv := functional_joint_measurable.comp ((hV.comp measurable_fst).prodMk harg)
  simp_rw [map_sub]
  exact hu.add (((hs.sub hQ).const_mul (-Λ)).exp.const_mul θ |>.mul (hv.sub hu))

end SHE.JointInterpolationAlgebra

namespace SHE.ActualMeanKernel
open Set Filter MeasureTheory ProbabilityTheory AddCircle Real StoppedFourier
  NativeHeatObservation DyadicApproximation WordRecursion CutoffWordLevel CutoffWordHistories
  CutoffCarriers NativeRandomKernel QuarterSpatialEvent
open scoped NNReal ENNReal
local instance meanInputTimeFields_nativePositive : Fact (0<2*π) := ⟨by positivity⟩
local instance meanInputTimeFields_exponentFinite : Fact ((2:ENNReal)≠⊤) := ⟨by simp⟩
local instance meanInputTimeFields_realSigma : MeasurableSpace RealL2 := borel _
local instance meanInputTimeFields_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance meanInputTimeFields_nativeSigma : MeasurableSpace CircleL2 := borel _
local instance meanInputTimeFields_nativeBorel : BorelSpace CircleL2 := ⟨rfl⟩
variable {Ω : Type} [MeasurableSpace Ω] {R : ReferenceData}
variable (L : CutoffWordLevel.Level R HeatCircle 1)

/-- Joint current-time/old-time/sample Borel dependence of the literal
mean input, including the exact collision/inactive extensions. -/
theorem meanInput_time_measurable (T : ℝ) (hT : ∀ x,L.terminal x=T)
    (k : ℕ) (mass ρ : ℝ) (hmass : 1≤mass) (hρ : 0≤ρ)
    (damping : ℝ) (hdamping : 0≤damping)
    (m : ℝ≥0→Ω→History HeatCircle k→WordRecursion.State (1+k))
    (hm : Measurable (fun z : (ℝ≥0×Ω)×History HeatCircle k=>m z.1.1 z.1.2 z.2))
    (V : ℝ≥0×Ω→RealL2) (hV : Measurable V) :
    Measurable (fun z : (Fin k→ℝ)×(ℝ≥0×Ω)=>
      meanInput L k mass ρ hmass hρ damping z.2.1 (m z.2.1) (fun ω=>V (z.2.1,ω)) (z.1,z.2.2)) := by
  let G : (((Fin k→ℝ)×(ℝ≥0×Ω))×(HeatCircle×HeatCircle))→ℂ :=
    fun z=>weightedSpatial L k damping z.1.2.1 z.1.2.1 (m z.1.2.1) z.1.1 z.1.2.2 z.2.1 z.2.2
  let M : ((Fin k→ℝ)×(ℝ≥0×Ω))→History HeatCircle k→WordRecursion.State (1+k) :=
    fun z p=>m z.2.1 z.2.2 p
  have hM : Measurable (fun z : ((Fin k→ℝ)×(ℝ≥0×Ω))×History HeatCircle k=>M z.1 z.2) :=
    hm.comp (measurable_fst.snd.prodMk measurable_snd)
  have hQ : Measurable (fun z : (Fin k→ℝ)×(ℝ≥0×Ω)=>(z.2.1:ℝ)) :=
    measurable_subtype_coe.comp measurable_snd.fst
  have hG : Measurable G := weightedSpatial_variable_measurable L k damping
    (fun z : (Fin k→ℝ)×(ℝ≥0×Ω)=>(z.2.1:ℝ)) (fun z=>(z.2.1:ℝ)) hQ hQ M hM Prod.fst measurable_fst
  have hb : ∀ z : (Fin k→ℝ)×(ℝ≥0×Ω),∃ B : ℝ,∀ y x,‖G (z,(y,x))‖≤B := by
    intro z
    obtain ⟨B,hB,hbound⟩ := weightedSpatial_uniform_bound L (X:=Ω) T hT k hdamping z.2.1 z.2.1 z.1
    exact ⟨B,fun y x=>hbound (m z.2.1) z.2.2 y x⟩
  have ha := NativeRandomKernel.action_measurable hG hb
    (fun z : (Fin k→ℝ)×(ℝ≥0×Ω)=>embed (V z.2))
    (embed.continuous.measurable.comp (hV.comp measurable_snd))
  have hQb := (OneInputOperator.besselHalf mass ρ hmass hρ).continuous.measurable.comp ha
  convert! hQb using 1

theorem meanAverage_time_measurable (T : ℝ) (hT : ∀ x,L.terminal x=T)
    (k : ℕ) (ν : Measure (Fin k→ℝ)) [SFinite ν]
    (mass ρ : ℝ) (hmass : 1≤mass) (hρ : 0≤ρ)
    (damping : ℝ) (hdamping : 0≤damping)
    (m : ℝ≥0→Ω→History HeatCircle k→WordRecursion.State (1+k))
    (hm : Measurable (fun z : (ℝ≥0×Ω)×History HeatCircle k=>m z.1.1 z.1.2 z.2))
    (V : ℝ≥0×Ω→RealL2) (hV : Measurable V) :
    Measurable (fun z : ℝ≥0×Ω=>meanAverage L k ν mass ρ hmass hρ damping z.1
      (m z.1) (fun ω=>V (z.1,ω)) z.2) :=
  (meanInput_time_measurable L T hT k mass ρ hmass hρ damping hdamping m hm V hV).stronglyMeasurable.integral_prod_left'.measurable

end SHE.ActualMeanKernel
