module

public import SHE.NativeMultiplierTrace
public import SHE.KernelActionFields
public import SHE.NativeHaarKernel
public import SHE.NativeRealNoise
public import SHE.HilbertColumns

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2500000
namespace SHE.NativeMultiplierColumnFields
open Set MeasureTheory ProbabilityTheory Real AddCircle StoppedFourier NativeHeatObservation NativeRandomKernel
open scoped NNReal ENNReal
local instance nativeMultiplierColumnFields_period : Fact (0<2*π):=⟨by positivity⟩
local instance nativeMultiplierColumnFields_unit : Fact (0<(1:ℝ)):=⟨zero_lt_one⟩
local instance nativeMultiplierColumnFields_sigma : MeasurableSpace CircleL2:=borel _
local instance nativeMultiplierColumnFields_borel : BorelSpace CircleL2:=⟨rfl⟩
local instance nativeMultiplierColumnFields_second : SecondCountableTopology CircleL2:=
  (_root_.fourierBasis (T:=2*π)).repr.toHomeomorph.secondCountableTopology
local instance nativeMultiplierColumnFields_unitSigma : MeasurableSpace CircleHeat.CircleL2:=borel _
local instance nativeMultiplierColumnFields_unitBorel : BorelSpace CircleHeat.CircleL2:=⟨rfl⟩
variable {P : Type*} [MeasurableSpace P]

def kernel (b : P×HeatCircle→ℂ) (t : P→ℝ) (p : P×(HeatCircle×HeatCircle)) : ℂ:=
  b (p.1,p.2.2)*ProfileVariance.heatPhysical (t p.1) p.2.2 p.2.1

theorem kernel_measurable {b : P×HeatCircle→ℂ} (hb : Measurable b) {t : P→ℝ} (ht : Measurable t) :
    Measurable (kernel b t) :=
  (hb.comp (measurable_fst.prodMk measurable_snd.snd)).mul
    (ProfileVariance.heatPhysical_joint_measurable.comp
      (((ht.comp measurable_fst).prodMk measurable_snd.snd).prodMk measurable_snd.fst))

theorem heat_bound {t : ℝ} (ht : 0<t) (x y : HeatCircle) :
    ‖ProfileVariance.heatPhysical t x y‖≤1+heatConstant*(t/2)^(-(1/2:ℝ)) := by
  rw [←WordRecursion.heatPhysical_real ht x y,Complex.norm_real,Real.norm_eq_abs]
  exact WordRecursion.heatPhysical_re_bound ht le_rfl x y

theorem kernel_bound {b : P×HeatCircle→ℂ} (cap : P→ℝ) (hb : ∀ p x,‖b (p,x)‖≤cap p)
    {t : P→ℝ} (ht : ∀ p,0<t p) (p : P) (y x : HeatCircle) :
    ‖kernel b t (p,(y,x))‖≤cap p*(1+heatConstant*(t p/2)^(-(1/2:ℝ))) := by
  rw [kernel,norm_mul]
  exact mul_le_mul (hb p x) (heat_bound (ht p) x y) (norm_nonneg _) ((norm_nonneg (b (p,x))).trans (hb p x))

theorem row_bound {b : P×HeatCircle→ℂ} (hbm : Measurable b) (cap : P→ℝ)
    (hb : ∀ p x,‖b (p,x)‖≤cap p) (p : P) :
    ∀ᵐ x : HeatCircle ∂haarAddCircle,‖NativeRandomRows.nativeRow b p x‖≤cap p := by
  filter_upwards [NativeRandomRows.nativeRow_ae_cap hbm cap hb p] with x hx
  rw [hx]
  exact hb p x

/-- Literal multiplier/heat action of the canonical kernel. Parameter
caps are used only sectionwise and need not be measurable or uniform. -/
theorem operator_eq {b : P×HeatCircle→ℂ} (hbm : Measurable b) (cap : P→ℝ)
    (hb : ∀ p x,‖b (p,x)‖≤cap p) {t : P→ℝ} (htm : Measurable t) (ht : ∀ p,0<t p) (p : P)
    (v : CircleL2) :
    integralOperator (kernel b t) p v=
      NativeMultiplierTrace.multiplier (NativeRandomRows.nativeRow b p) (cap p)
        (row_bound hbm cap hb p)
        (circleHeatOperator (t p) (ht p).le v) := by
  change integralOperator (fun z : Unit×(HeatCircle×HeatCircle)=>kernel b t (p,z.2)) () v=_
  have hF : Measurable (fun z : Unit×(HeatCircle×HeatCircle)=>kernel b t (p,z.2)):=
    (kernel_measurable hbm htm).comp (measurable_const.prodMk measurable_snd)
  have hB : 0≤cap p*(1+heatConstant*(t p/2)^(-(1/2:ℝ))):=
    mul_nonneg ((norm_nonneg (b (p,0))).trans (hb p 0))
      (add_nonneg zero_le_one (mul_nonneg heatConstant_pos.le (rpow_nonneg (div_nonneg (ht p).le (by norm_num)) _)))
  exact NativeMultiplierTrace.integralOperator_eq_multiplier_heat hF hB
    (fun _ y x=>kernel_bound cap hb ht p y x) (ht p)
    (fun z : Unit×HeatCircle=>b (p,z.2)) (NativeRandomRows.nativeRow b p) (cap p) _ ()
    (NativeRandomRows.nativeRow_ae_cap hbm cap hb p) (fun _ _=>rfl) v

/-- The actual Q M_b S_t column with its original native Haar input. -/
def column {Λ ρ : ℝ} (hΛ : 1≤Λ) (hρ : 0≤ρ) (b : P×HeatCircle→ℂ) (t : P→ℝ)
    {m U : ℝ} (hm : 0<m) (c : P→FiniteHaar.EllipticField m U) (p : P) (q : FiniteHaar.HaarNode) : CircleL2:=
  OneInputOperator.besselHalf Λ ρ hΛ hρ (integralOperator (kernel b t) p
    (CircleNormalization.push (FiniteHaar.globalHaarColumn q (c p).1)))

/-- All physical columns are genuinely Borel for an arbitrary supplied
sigma algebra, so the same result applies to predictable parameters. -/
theorem column_measurable {Λ ρ m U : ℝ} (hΛ : 1≤Λ) (hρ : 0≤ρ) (hm : 0<m)
    {b : P×HeatCircle→ℂ} (hbm : Measurable b) (cap : P→ℝ) (hb : ∀ p x,‖b (p,x)‖≤cap p)
    {t : P→ℝ} (htm : Measurable t) (ht : ∀ p,0<t p)
    (c : P→FiniteHaar.EllipticField m U) (hc : Measurable c) (q : FiniteHaar.HaarNode) :
    Measurable (fun p=>column hΛ hρ b t hm c p q) := by
  have hinput:=NativeHaarKernel.factor_column_measurable m U hm c hc q
  simp only [NativeHaarKernel.factor_basis] at hinput
  have ha:=NativeRandomKernel.action_measurable (kernel_measurable hbm htm)
    (fun p=>⟨cap p*(1+heatConstant*(t p/2)^(-(1/2:ℝ))),kernel_bound cap hb ht p⟩)
    (fun p=>CircleNormalization.push (FiniteHaar.globalHaarColumn q (c p).1)) hinput
  exact (OneInputOperator.besselHalf Λ ρ hΛ hρ).continuous.measurable.comp ha

end SHE.NativeMultiplierColumnFields
