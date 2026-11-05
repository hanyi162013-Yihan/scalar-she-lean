module

public import SHEStochastic.ScalarHeatFourierEnergy
public import SHEStochastic.RealCausalHeatKernel
public import SHE.JointLpRepresentative
public import SHEStochastic.MeasurableHilbertL2Realization

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section

namespace SHEStochastic.ScalarLipschitzHeatColumn
open MeasureTheory SHE SHE.PredictableL2 SHE.StoppedFourier SHE.DyadicApproximation SHE.FiniteHaar AddCircle
open scoped NNReal ENNReal

local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance : Fact (0 < 2*Real.pi) := ⟨by positivity⟩
local instance : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by simp⟩
local notation "ν" => haarAddCircle (T := 2*Real.pi)
local notation "Noise" => Lp ℝ 2 ν
local instance : SecondCountableTopology CircleHeat.CircleL2 :=
  (_root_.fourierBasis (T := (1 : ℝ))).repr.toHomeomorph.secondCountableTopology
local instance : SecondCountableTopology RealL2 := realCircleIdentification.toHomeomorph.secondCountableTopology
local instance : MeasurableSpace RealL2 := borel _
local instance : BorelSpace RealL2 := ⟨rfl⟩
local instance : MeasurableSpace Noise := borel _
local instance : BorelSpace Noise := ⟨rfl⟩
local instance : SecondCountableTopology Noise :=
  NativePhysicalState.equivalence.symm.toHomeomorph.secondCountableTopology
local notation "φ" => NativeFourierHeatCoordinate.coordinate
local notation "w" => NativeFourierHeatCoordinate.weight

/-- The spatial section of the actual positive heat kernel viewed
in the original real L² state space. -/
def sectionVector (r : ℝ) (y : HeatCircle) : RealL2 :=
  NativePhysicalState.pull (ContinuousMap.toLp 2 ν ℝ (RealCausalHeatKernel.value y r))

theorem section_measurable : Measurable (fun p : ℝ×HeatCircle => sectionVector p.1 p.2) := by
  have h := MeasurableHilbertL2Realization.measurable
    (fun p : (ℝ×HeatCircle)×HeatCircle => RealCausalHeatKernel.value p.1.2 p.1.1 p.2)
    RealCausalHeatKernel.joint_center_measurable
    (fun p => ContinuousMap.toLp 2 ν ℝ (RealCausalHeatKernel.value p.2 p.1))
    (fun p => ContinuousMap.coeFn_toLp ν (𝕜 := ℝ) (p := (2 : ENNReal)) (RealCausalHeatKernel.value p.2 p.1))
  exact NativePhysicalState.pull.continuous.measurable.comp h

theorem section_continuous {r : ℝ} (hr : 0<r) : Continuous (sectionVector r) :=
  NativePhysicalState.pull.continuous.comp
    ((ContinuousMap.toLp 2 ν ℝ).continuous.comp (RealCausalHeatKernel.continuous_center hr))

theorem section_zero {r : ℝ} (hr : r≤0) (y : HeatCircle) : sectionVector r y=0 := by
  rw [sectionVector,RealCausalHeatKernel.nonpos hr,map_zero,map_zero]

theorem section_mode {r : ℝ} (hr : 0<r) (y : HeatCircle) (ψ : ℂ →L[ℝ] ℝ) (n : ℤ) :
    φ ψ n (sectionVector r y)=Real.exp (-r*(n : ℝ)^2)*w ψ n y := by
  rw [NativeFourierHeatCoordinate.coordinate_integral,sectionVector,NativePhysicalState.push_pull]
  refine (integral_congr_ae ?_).trans (NativeFourierHeatCoordinate.weight_average ψ n hr y)
  filter_upwards [ContinuousMap.coeFn_toLp ν (𝕜 := ℝ) (p := (2 : ENNReal)) (RealCausalHeatKernel.value y r)]
    with x hx
  rw [hx]

/-- One exact spatial white-noise column at positive age, defined
for any square-integrable coefficient, without an upper bound. -/
def column (r : ℝ) (a v : Noise) : RealL2 :=
  ∫ y,(JointLpRepresentative.representative ν (a,y)*v y) • sectionVector r y ∂ν

theorem column_measurable (v : Noise) :
    Measurable (fun p : ℝ×Noise => column p.1 p.2 v) := by
  have hA : Measurable (fun p : (ℝ×Noise)×HeatCircle =>
      JointLpRepresentative.representative ν (p.1.2,p.2)*v p.2) :=
    ((JointLpRepresentative.representative_measurable ν).comp
      (measurable_fst.snd.prodMk measurable_snd)).mul ((Lp.stronglyMeasurable v).measurable.comp measurable_snd)
  have hK : Measurable (fun p : (ℝ×Noise)×HeatCircle => sectionVector p.1.1 p.2) :=
    section_measurable.comp (measurable_fst.fst.prodMk measurable_snd)
  exact ((hA.smul hK).stronglyMeasurable.integral_prod_right').measurable

theorem column_zero {r : ℝ} (hr : r≤0) (a v : Noise) : column r a v=0 := by
  simp only [column,section_zero hr,smul_zero,integral_zero]

def weighted (a : Noise) (k : C(HeatCircle,ℝ)) : Noise :=
  ContinuousKernelLpAction.operator ν a k

theorem weighted_ae (a : Noise) (k : C(HeatCircle,ℝ)) :
    weighted a k =ᵐ[ν] fun y => k y*a y :=
  ContinuousKernelLpAction.operator_ae ν a k

theorem column_mode {r : ℝ} (hr : 0<r) (a v : Noise) (ψ : ℂ →L[ℝ] ℝ) (n : ℤ) :
    φ ψ n (column r a v)=Real.exp (-r*(n : ℝ)^2)*inner ℝ (weighted a (w ψ n)) v := by
  have hA : Integrable (fun y => JointLpRepresentative.representative ν (a,y)*v y) ν :=
    ((Lp.memLp a).integrable_mul (Lp.memLp v)).congr
      ((JointLpRepresentative.representative_ae ν a).mono (fun y hy => congrArg (fun z => z*v y) hy.symm))
  obtain ⟨B,hB⟩ := (isCompact_range (section_continuous hr)).isBounded.exists_norm_le
  have hI : Integrable (fun y => (JointLpRepresentative.representative ν (a,y)*v y) • sectionVector r y) ν :=
    hA.smul_bdd B (section_continuous hr).aestronglyMeasurable (ae_of_all _ fun y => hB _ ⟨y,rfl⟩)
  rw [column,←(φ ψ n).integral_comp_comm hI,L2.inner_def,←integral_const_mul]
  apply integral_congr_ae
  filter_upwards [JointLpRepresentative.representative_ae ν a,weighted_ae a (w ψ n)] with y ha hw
  change (φ ψ n) ((JointLpRepresentative.representative ν (a,y)*v y) • sectionVector r y) =
    Real.exp (-r*(n : ℝ)^2)*inner ℝ (weighted a (w ψ n) y) (v y)
  rw [map_smul,smul_eq_mul,section_mode hr,ha,hw,RCLike.inner_apply,conj_trivial]
  ring

end SHEStochastic.ScalarLipschitzHeatColumn
