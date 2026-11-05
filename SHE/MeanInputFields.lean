module

public import SHE.KernelActionFields
public import SHE.WeightedMeanInputEnergy
public import SHE.WeightedNoiseSupport

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 2500000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHE.ActualMeanKernel
open Set Filter MeasureTheory ProbabilityTheory AddCircle Real StoppedFourier
  NativeHeatObservation DyadicApproximation WordRecursion CutoffWordLevel CutoffWordHistories
  CutoffCarriers NativeRandomKernel QuarterSpatialEvent
open scoped ENNReal
local instance meanInputFields_nativePositive : Fact (0<2*π) := ⟨by positivity⟩
local instance meanInputFields_exponentFinite : Fact ((2:ENNReal)≠⊤) := ⟨by simp⟩
local instance meanInputFields_realSigma : MeasurableSpace RealL2 := borel _
local instance meanInputFields_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance meanInputFields_nativeSigma : MeasurableSpace CircleL2 := borel _
local instance meanInputFields_nativeBorel : BorelSpace CircleL2 := ⟨rfl⟩
variable {Ω : Type} [MeasurableSpace Ω] {R : ReferenceData}
variable (L : CutoffWordLevel.Level R HeatCircle 1)

def meanInput (k : ℕ) (mass ρ : ℝ) (hmass : 1≤mass) (hρ : 0≤ρ)
    (damping q : ℝ) (m : Ω→History HeatCircle k→WordRecursion.State (1+k))
    (V : Ω→RealL2) (z : (Fin k→ℝ)×Ω) : CircleL2 :=
  OneInputOperator.besselHalf mass ρ hmass hρ
    (integralOperator (weightedField L k damping q q m z.1) z.2 (embed (V z.2)))

/-- Joint old-time/sample measurability of the actual mean input. The
coarse bound is permitted to depend on every old gap; no old-time
uniform cap or point evaluation on L² is used. -/
theorem meanInput_measurable (T : ℝ) (hT : ∀ x,L.terminal x=T)
    (k : ℕ) (mass ρ : ℝ) (hmass : 1≤mass) (hρ : 0≤ρ)
    (damping q : ℝ) (hdamping : 0≤damping)
    (m : Ω→History HeatCircle k→WordRecursion.State (1+k))
    (hm : Measurable (fun z : Ω×History HeatCircle k=>m z.1 z.2))
    (V : Ω→RealL2) (hV : Measurable V) :
    Measurable (meanInput L k mass ρ hmass hρ damping q m V) := by
  let G : (((Fin k→ℝ)×Ω)×(HeatCircle×HeatCircle))→ℂ :=
    fun z=>weightedSpatial L k damping q q m z.1.1 z.1.2 z.2.1 z.2.2
  let M : ((Fin k→ℝ)×Ω)→History HeatCircle k→WordRecursion.State (1+k) := fun z p=>m z.2 p
  have hM : Measurable (fun z : ((Fin k→ℝ)×Ω)×History HeatCircle k=>M z.1 z.2) :=
    hm.comp (measurable_fst.snd.prodMk measurable_snd)
  have hG : Measurable G := weightedSpatial_variable_measurable L k damping
    (fun _ : (Fin k→ℝ)×Ω=>q) (fun _=>q) measurable_const measurable_const
    M hM Prod.fst measurable_fst
  have hb : ∀ z : (Fin k→ℝ)×Ω,∃ B : ℝ,∀ y x,‖G (z,(y,x))‖≤B := by
    intro z
    obtain ⟨B,hB,hbound⟩ := weightedSpatial_uniform_bound L (X:=Ω) T hT k hdamping q q z.1
    exact ⟨B,fun y x=>hbound m z.2 y x⟩
  have ha := NativeRandomKernel.action_measurable hG hb
    (fun z : (Fin k→ℝ)×Ω=>embed (V z.2))
    (embed.continuous.measurable.comp (hV.comp measurable_snd))
  have hQ := (OneInputOperator.besselHalf mass ρ hmass hρ).continuous.measurable.comp ha
  convert! hQ using 1

theorem meanInput_zero_of_not_active (T : ℝ) (hT : ∀ x,L.terminal x=T)
    (k : ℕ) (mass ρ : ℝ) (hmass : 1≤mass) (hρ : 0≤ρ)
    (damping q : ℝ) (m : Ω→History HeatCircle k→WordRecursion.State (1+k))
    (V : Ω→RealL2) (t : Fin k→ℝ) (ha : ¬active L T k q t) (ω : Ω) :
    meanInput L k mass ρ hmass hρ damping q m V (t,ω)=0 := by
  unfold meanInput
  rw [weightedField_zero_of_not_active L T hT k damping q q t m ha,integralOperator_zero]
  simp only [ContinuousLinearMap.zero_apply,map_zero]

def meanAverage (k : ℕ) (ν : Measure (Fin k→ℝ)) (mass ρ : ℝ) (hmass : 1≤mass) (hρ : 0≤ρ)
    (damping q : ℝ) (m : Ω→History HeatCircle k→WordRecursion.State (1+k))
    (V : Ω→RealL2) (ω : Ω) : CircleL2 :=
  ∫ t,meanInput L k mass ρ hmass hρ damping q m V (t,ω) ∂ν

end SHE.ActualMeanKernel
