module

public import SHE.KernelActionFields
public import SHE.NativeHaarKernel
public import SHE.HilbertColumns

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

namespace SHE.NativeKernelHaarColumns
open MeasureTheory Set AddCircle StoppedFourier FiniteHaar
open scoped ENNReal
local instance nativeKernelHaarColumns_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
local instance nativeKernelHaarColumns_pfinite : Fact ((2:ENNReal)≠⊤) := ⟨by simp⟩
local instance nativeKernelHaarColumns_plower : Fact (1≤(2:ENNReal)) := ⟨by norm_num⟩
local instance nativeKernelHaarColumns_sigma : MeasurableSpace CircleL2 := borel _
local instance nativeKernelHaarColumns_borel : BorelSpace CircleL2 := ⟨rfl⟩
local instance nativeKernelHaarColumns_unitSigma : MeasurableSpace CircleHeat.CircleL2 := borel _
local instance nativeKernelHaarColumns_unitBorel : BorelSpace CircleHeat.CircleL2 := ⟨rfl⟩
local instance nativeKernelHaarColumns_second : SecondCountableTopology CircleL2 :=
  (_root_.fourierBasis (T:=2*Real.pi)).repr.toHomeomorph.secondCountableTopology
abbrev Space := HilbertColumns.Space HaarNode CircleL2
local instance nativeKernelHaarColumns_spaceSigma : MeasurableSpace Space := borel _
local instance nativeKernelHaarColumns_spaceBorel : BorelSpace Space := ⟨rfl⟩
variable {P : Type*} [MeasurableSpace P]

def column {mass ρ m U:ℝ} (hmass:1≤mass) (hρ:0≤ρ) (hm:0<m)
    (F:P×(HeatCircle×HeatCircle)→ℂ) (c:P→EllipticField m U) (p:P) (j:HaarNode):CircleL2 :=
  OneInputOperator.besselHalf mass ρ hmass hρ
    (NativeRandomKernel.integralOperator F p
      (CircleNormalization.push (globalHaarColumn j (c p).1)))

/-- The actual bounded spatial kernel followed by the original Haar
factor has square-summable native output columns at every parameter. -/
theorem summable {mass ρ m U:ℝ} (hmass:1≤mass) (hρ:0≤ρ) (hm:0<m)
    {F:P×(HeatCircle×HeatCircle)→ℂ} (hF:Measurable F)
    (hb:∀p,∃B:ℝ,∀y x,‖F (p,(y,x))‖≤B)
    (c:P→EllipticField m U) (p:P):
    Summable (fun j=>‖column hmass hρ hm F c p j‖^2) := by
  obtain ⟨B,hB⟩:=hb p
  have hB0:0≤B:=(norm_nonneg (F (p,(0,0)))).trans (hB 0 0)
  let G:Unit×(HeatCircle×HeatCircle)→ℂ:=fun z=>F (p,z.2)
  have hG:Measurable G:=hF.comp (measurable_const.prodMk measurable_snd)
  have he:=NativeRandomKernel.negative_synthesis_eq hmass hρ hG hB0 (fun _ y x=>hB y x) ()
  have hs:=KernelOperator.synthesis_right_trace
    (NativeRandomKernel.negativeKernel _ _ hmass hρ G ())
    (NativeHaarKernel.factor m U hm (c p))
    (_root_.fourierBasis (T:=2*Real.pi)) (_root_.fourierBasis (T:=2*Real.pi))
    NativeHaarKernel.inputBasis
  have hid(j:HaarNode):
      ((KernelOperator.synthesis (NativeRandomKernel.negativeKernel _ _ hmass hρ G ())).comp
        (NativeHaarKernel.factor m U hm (c p))) (NativeHaarKernel.inputBasis j)=
      column hmass hρ hm F c p j := by
    rw [he]
    simp only [ContinuousLinearMap.comp_apply,NativeHaarKernel.factor_basis,column]
    rfl
  simpa only [hid] using hs.1

def columns {mass ρ m U:ℝ} (hmass:1≤mass) (hρ:0≤ρ) (hm:0<m)
    {F:P×(HeatCircle×HeatCircle)→ℂ} (hF:Measurable F)
    (hb:∀p,∃B:ℝ,∀y x,‖F (p,(y,x))‖≤B)
    (c:P→EllipticField m U) (p:P):Space :=
  HilbertColumns.ofSummable (column hmass hρ hm F c p) (summable hmass hρ hm hF hb c p)

theorem columns_apply {mass ρ m U:ℝ} (hmass:1≤mass) (hρ:0≤ρ) (hm:0<m)
    {F:P×(HeatCircle×HeatCircle)→ℂ} (hF:Measurable F)
    (hb:∀p,∃B:ℝ,∀y x,‖F (p,(y,x))‖≤B)
    (c:P→EllipticField m U) (p:P) (j:HaarNode):
    columns hmass hρ hm hF hb c p j=column hmass hρ hm F c p j := rfl

theorem columns_norm_sq {mass ρ m U:ℝ} (hmass:1≤mass) (hρ:0≤ρ) (hm:0<m)
    {F:P×(HeatCircle×HeatCircle)→ℂ} (hF:Measurable F)
    (hb:∀p,∃B:ℝ,∀y x,‖F (p,(y,x))‖≤B)
    (c:P→EllipticField m U) (p:P):
    ‖columns hmass hρ hm hF hb c p‖^2=∑'j,‖column hmass hρ hm F c p j‖^2 :=
  HilbertColumns.norm_sq _

/-- Joint measurability needs only sectionwise finite spatial caps;
no bound uniform in the recursive old-time gaps is imposed. -/
theorem columns_measurable {mass ρ m U:ℝ} (hmass:1≤mass) (hρ:0≤ρ) (hm:0<m)
    {F:P×(HeatCircle×HeatCircle)→ℂ} (hF:Measurable F)
    (hb:∀p,∃B:ℝ,∀y x,‖F (p,(y,x))‖≤B)
    (c:P→EllipticField m U) (hc:Measurable c):
    Measurable (columns hmass hρ hm hF hb c) := by
  apply HilbertColumns.measurable_of_columns
  intro j
  apply (OneInputOperator.besselHalf mass ρ hmass hρ).continuous.measurable.comp
  apply NativeRandomKernel.action_measurable hF hb
  simpa only [NativeHaarKernel.factor_basis] using
    NativeHaarKernel.factor_column_measurable m U hm c hc j

end SHE.NativeKernelHaarColumns
