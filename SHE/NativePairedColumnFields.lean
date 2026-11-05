module

public import SHE.NativeMultiplierHilbertColumns
public import SHE.ScalarHeatCompleteGamma
public import SHE.NativeColumnProcesses

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
namespace SHE.NativePairedColumnFields
open Set MeasureTheory AddCircle StoppedFourier FiniteHaar NativeMultiplierHilbertColumns
open scoped ENNReal NNReal
local instance nativePairedColumnFields_period : Fact (0<2*Real.pi):=⟨by positivity⟩
local instance nativePairedColumnFields_unit : Fact (0<(1:ℝ)):=⟨zero_lt_one⟩
local instance nativePairedColumnFields_sigma : MeasurableSpace CircleL2:=borel _
local instance nativePairedColumnFields_borel : BorelSpace CircleL2:=⟨rfl⟩
local instance nativePairedColumnFields_unitSigma : MeasurableSpace CircleHeat.CircleL2:=borel _
local instance nativePairedColumnFields_unitBorel : BorelSpace CircleHeat.CircleL2:=⟨rfl⟩
local instance nativePairedColumnFields_second : SecondCountableTopology CircleL2:=
  (_root_.fourierBasis (T:=2*Real.pi)).repr.toHomeomorph.secondCountableTopology
local instance nativePairedColumnFields_spaceSigma : MeasurableSpace Space:=borel _
local instance nativePairedColumnFields_spaceBorel : BorelSpace Space:=⟨rfl⟩
variable {P : Type*} [MeasurableSpace P]
variable {Λ ρ m U : ℝ} (hΛ : 1≤Λ) (hρ : 0≤ρ) (hρhalf : ρ<1/2) (hm : 0<m)
variable (B : ℝ) (b : Fin 6→P×HeatCircle→ℂ) (hbm : ∀ i,Measurable (b i))
variable (hb : ∀ i p x,‖b i (p,x)‖≤B)
variable (t : P→ℝ) (htm : Measurable t) (ht : ∀ p,0<t p) (ht1 : ∀ p,t p≤1)

def single (i : Fin 6) (c : P→EllipticField m U) (p : P) : Space:=
  columns hΛ hρ hρhalf hm (hbm i) (fun _=>B) (hb i) htm ht ht1 c p

theorem single_measurable (i : Fin 6) (c : P→EllipticField m U) (hc : Measurable c) :
    Measurable (single hΛ hρ hρhalf hm B b hbm hb t htm ht ht1 i c):=
  columns_measurable hΛ hρ hρhalf hm (hbm i) (fun _=>B) (hb i) htm ht ht1 c hc

theorem single_energy (i : Fin 6) (c : P→EllipticField m U) (p : P) :
    ‖single hΛ hρ hρhalf hm B b hbm hb t htm ht ht1 i c p‖^2≤
      U*((1+2*HeatTrace.fractionalGaussianIntegral ρ)*(t p)^(ρ-1/2))*B^2 := by
  have hs:=trace hΛ hρ hρhalf hm (hbm i) (fun _=>B) (hb i) htm ht ht1 c p
  rw [HilbertColumns.norm_sq]
  refine hs.2.trans ?_
  have hrow : ‖NativeRandomRows.nativeRow (b i) p‖^2≤B^2:=by
    rw [L2_norm_sq_eq_integral]
    calc
      _≤∫ _ : HeatCircle,B^2 ∂haarAddCircle:=by
        apply integral_mono_ae ((memLp_two_iff_integrable_sq_norm (Lp.stronglyMeasurable (NativeRandomRows.nativeRow (b i) p)).aestronglyMeasurable).mp (Lp.memLp _)) (integrable_const _)
        filter_upwards [NativeMultiplierColumnFields.row_bound (hbm i) (fun _=>B) (hb i) p] with x hx
        exact pow_le_pow_left₀ (norm_nonneg _) hx 2
      _=B^2:=by simp
  exact mul_le_mul_of_nonneg_left hrow (mul_nonneg
    (elliptic_upper_nonneg (c p).1 m U hm (c p).2.2)
    (mul_nonneg (by linarith [HeatTrace.fractionalGaussianIntegral_pos hρhalf]) (Real.rpow_nonneg (ht p).le _)))

def paired (c0 c1 r0 r1 : P→EllipticField m U) (p : P) : Space:=
  single hΛ hρ hρhalf hm B b hbm hb t htm ht ht1 0 c0 p-
  single hΛ hρ hρhalf hm B b hbm hb t htm ht ht1 3 r0 p-
  single hΛ hρ hρhalf hm B b hbm hb t htm ht ht1 2 c1 p+
  single hΛ hρ hρhalf hm B b hbm hb t htm ht ht1 5 r1 p

theorem paired_measurable (c0 c1 r0 r1 : P→EllipticField m U)
    (hc0 : Measurable c0) (hc1 : Measurable c1) (hr0 : Measurable r0) (hr1 : Measurable r1) :
    Measurable (paired hΛ hρ hρhalf hm B b hbm hb t htm ht ht1 c0 c1 r0 r1):=
  (((single_measurable hΛ hρ hρhalf hm B b hbm hb t htm ht ht1 0 c0 hc0).sub
    (single_measurable hΛ hρ hρhalf hm B b hbm hb t htm ht ht1 3 r0 hr0)).sub
    (single_measurable hΛ hρ hρhalf hm B b hbm hb t htm ht ht1 2 c1 hc1)).add
    (single_measurable hΛ hρ hρhalf hm B b hbm hb t htm ht ht1 5 r1 hr1)

theorem four_norm {E : Type*} [NormedAddCommGroup E] (x y z w : E) :
    ‖x-y-z+w‖^2≤4*(‖x‖^2+‖y‖^2+‖z‖^2+‖w‖^2) := by
  have h0:=ScalarHeatCompleteGamma.norm_add_sq_le (x-y) (w-z)
  have h1:=ScalarHeatCompleteGamma.norm_add_sq_le x (-y)
  have h2:=ScalarHeatCompleteGamma.norm_add_sq_le w (-z)
  rw [norm_neg,←sub_eq_add_neg] at h1 h2
  rw [show x-y-z+w=(x-y)+(w-z) by abel]
  nlinarith

/-- Honest coarse trace energy of the WHOLE paired Gamma, sufficient
for stochastic integrability. Sharp six-slot estimates are imposed only
after constructing this literal infinite-column predictable field. -/
theorem paired_energy (c0 c1 r0 r1 : P→EllipticField m U) (p : P) :
    ‖paired hΛ hρ hρhalf hm B b hbm hb t htm ht ht1 c0 c1 r0 r1 p‖^2≤
      16*U*((1+2*HeatTrace.fractionalGaussianIntegral ρ)*(t p)^(ρ-1/2))*B^2 := by
  have h0:=single_energy hΛ hρ hρhalf hm B b hbm hb t htm ht ht1 0 c0 p
  have h1:=single_energy hΛ hρ hρhalf hm B b hbm hb t htm ht ht1 3 r0 p
  have h2:=single_energy hΛ hρ hρhalf hm B b hbm hb t htm ht ht1 2 c1 p
  have h3:=single_energy hΛ hρ hρhalf hm B b hbm hb t htm ht ht1 5 r1 p
  exact (four_norm _ _ _ _).trans (by nlinarith)

end SHE.NativePairedColumnFields
