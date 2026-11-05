module

public import SHEStochastic.MatrixPointRowDomination
public import SHEStochastic.MatrixPointHeatInput
public import SHEStochastic.UnboundedGlobalJointMoments
public import SHEStochastic.NativeInputPairing

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
noncomputable section

namespace SHEStochastic.MatrixPointJointMoments
open MeasureTheory SHE SHE.PredictableL2 SHE.StoppedFourier SHE.FiniteHaar MatrixInfiniteHaar HeatParameterCover
open scoped NNReal ENNReal
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance : Fact (0 < 2*Real.pi) := ⟨by positivity⟩
variable {d Ω : Type*} [Fintype d] [DecidableEq d] [MeasurableSpace Ω]
local instance : MeasurableSpace (Input (d := d)) := borel _
local instance : BorelSpace (Input (d := d)) := ⟨rfl⟩

def constant_holder : HolderWith (0 : ℝ≥0) (1/2) (fun _ : ℝ => (1 : ℝ)) := by
  intro x y
  simp

def geometryConstant (H : ℝ≥0) : ℝ≥0∞ :=
  UnboundedGlobalJointMoments.jointConstant (fun _ : ℝ => (1 : ℝ)) 0 (1/2) 0 H

theorem geometryConstant_finite (H : ℝ≥0) : geometryConstant H < ⊤ :=
  UnboundedGlobalJointMoments.jointConstant_finite _ _ _ _ _

def scalarFamily (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (T : ℝ≥0) (x : HeatCircle)
    (p : ℝ≥0 × Ω) : Lp ℝ 2 (AddCircle.haarAddCircle (T := 2*Real.pi)) :=
  UnboundedHeatFamily.family F (fun _ => (0 : Lp ℝ 2 AddCircle.haarAddCircle)) stronglyMeasurable_const
    constant_holder (by norm_num) (by norm_num) T x p

variable (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ]
  (H : ℝ≥0) (U : ℝ) (hU : 0 ≤ U) (Q : ℝ≥0 × Ω → Profile d)
  (hUpper : ∀ p, (Q p).upper ≤ U)

include F hUpper in
/-- All matrix point-row brackets are dominated by the already proved
scalar additive heat geometry, independently of covariance orientations. -/
theorem family_bracket (p q : Parameter) (i : d) :
    ∀ᵐ ω ∂μ, (∫⁻ s, ENNReal.ofReal
      (‖MatrixPointHeatRows.row ((GlobalHeatParameter.time H p : ℝ)-(s : ℝ)) (Q (s,ω))
          (HeatParameterCoordinates.center p) i-
        MatrixPointHeatRows.row ((GlobalHeatParameter.time H q : ℝ)-(s : ℝ)) (Q (s,ω))
          (HeatParameterCoordinates.center q) i‖^2) ∂timeMeasure H) ≤
      (ENNReal.ofReal U*geometryConstant H)*ENNReal.ofReal (dist p q^(1/8 : ℝ)) := by
  have hs := UnboundedGlobalJointMoments.family_bracket F
    (fun _ => (0 : Lp ℝ 2 (AddCircle.haarAddCircle (T := 2*Real.pi)))) stronglyMeasurable_const
    constant_holder (by norm_num) (by norm_num) μ H p q
    (Filter.Eventually.of_forall (fun _ => (by simp : ‖(0 : Lp ℝ 2 AddCircle.haarAddCircle)‖ ≤ (0 : ℝ))))
  filter_upwards [hs] with ω hω
  change (∫⁻ s, ENNReal.ofReal
    (‖scalarFamily F (GlobalHeatParameter.time H p) (HeatParameterCoordinates.center p) (s,ω)-
      scalarFamily F (GlobalHeatParameter.time H q) (HeatParameterCoordinates.center q) (s,ω)‖^2)
      ∂timeMeasure H) ≤ geometryConstant H*ENNReal.ofReal
        (dist p q^UnboundedHeatIncrementCaps.exponent (1/2)) at hω
  have hexp : UnboundedHeatIncrementCaps.exponent (1/2) = (1/8 : ℝ) := by
    norm_num [UnboundedHeatIncrementCaps.exponent]
  rw [hexp] at hω
  calc
    _ ≤ ∫⁻ s, ENNReal.ofReal U*ENNReal.ofReal
        (‖scalarFamily F (GlobalHeatParameter.time H p) (HeatParameterCoordinates.center p) (s,ω)-
          scalarFamily F (GlobalHeatParameter.time H q) (HeatParameterCoordinates.center q) (s,ω)‖^2)
            ∂timeMeasure H := by
      apply lintegral_mono
      intro s
      have hb := MatrixPointRowDomination.bound (Q (s,ω))
        ((GlobalHeatParameter.time H p : ℝ)-(s : ℝ)) ((GlobalHeatParameter.time H q : ℝ)-(s : ℝ))
        (HeatParameterCoordinates.center p) (HeatParameterCoordinates.center q) i (hUpper (s,ω))
      simpa only [scalarFamily,UnboundedHeatFamily.difference_energy,Real.norm_eq_abs,abs_one,
        one_pow,mul_one] using hb
    _ = ENNReal.ofReal U*(∫⁻ s, ENNReal.ofReal
        (‖scalarFamily F (GlobalHeatParameter.time H p) (HeatParameterCoordinates.center p) (s,ω)-
          scalarFamily F (GlobalHeatParameter.time H q) (HeatParameterCoordinates.center q) (s,ω)‖^2)
            ∂timeMeasure H) := by rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ ≤ _ := (mul_le_mul_right hω (ENNReal.ofReal U)).trans_eq (mul_assoc _ _ _).symm

variable (hH : (H : ℝ) ≤ 1)
  (hQ : @Measurable ((ℝ≥0 × Ω) × AddCircle (1 : ℝ)) (Matrix d d ℝ)
    (F.predictable.prod inferInstance) inferInstance (fun z => (Q z.1).value z.2))

def input (p : Parameter) (i : d) : Process (E := Input (d := d)) F μ H :=
  MatrixPointHeatInput.input F μ H hH U hU Q hUpper hQ (GlobalHeatParameter.time H p)
    (GlobalHeatParameter.time_le_horizon H p) (HeatParameterCoordinates.center p) i

/-- The same bracket estimate holds for the genuine native L2 inputs,
including their actual chosen predictable representatives. -/
theorem input_bracket (p q : Parameter) (i : d) :
    ∀ᵐ ω ∂μ, (∫⁻ s, ENNReal.ofReal
      (‖(input F μ H U hU Q hUpper hH hQ p i-input F μ H U hU Q hUpper hH hQ q i) (s,ω)‖^2)
        ∂timeMeasure H) ≤
      (ENNReal.ofReal U*geometryConstant H)*ENNReal.ofReal (dist p q^(1/8 : ℝ)) := by
  let vp := input F μ H U hU Q hUpper hH hQ p i
  let vq := input F μ H U hU Q hUpper hH hQ q i
  have he : vp-vq =ᵐ[energyMeasure μ H] fun z =>
      MatrixPointHeatRows.row ((GlobalHeatParameter.time H p : ℝ)-(z.1 : ℝ)) (Q z)
        (HeatParameterCoordinates.center p) i-
      MatrixPointHeatRows.row ((GlobalHeatParameter.time H q : ℝ)-(z.1 : ℝ)) (Q z)
        (HeatParameterCoordinates.center q) i := by
    filter_upwards [ae_eq_of_ae_eq_trim (Lp.coeFn_sub vp vq),
      MatrixPointHeatInput.input_ae F μ H hH U hU Q hUpper hQ (GlobalHeatParameter.time H p)
        (GlobalHeatParameter.time_le_horizon H p) (HeatParameterCoordinates.center p) i,
      MatrixPointHeatInput.input_ae F μ H hH U hU Q hUpper hQ (GlobalHeatParameter.time H q)
        (GlobalHeatParameter.time_le_horizon H q) (HeatParameterCoordinates.center q) i] with z hs hp hq
    rw [hs]
    exact congrArg₂ HSub.hSub hp hq
  have hs := (Measure.measurePreserving_swap (μ := μ) (ν := timeMeasure H)).quasiMeasurePreserving.ae he
  filter_upwards [Measure.ae_ae_of_ae_prod hs,family_bracket F μ H U Q hUpper p q i] with ω he hb
  exact (lintegral_congr_ae (he.mono fun _ hz => congrArg (fun z => ENNReal.ofReal (‖z‖^2)) hz)).trans_le hb

def momentConstant (U : ℝ) (H : ℝ≥0) (k : ℕ) : ℝ≥0∞ :=
  (NativeScalarBDG.constant k : ℝ≥0∞)*(ENNReal.ofReal U*geometryConstant H)^(2^k)

theorem momentConstant_finite (U : ℝ) (H : ℝ≥0) (k : ℕ) : momentConstant U H k < ⊤ := by
  have hg := geometryConstant_finite H
  unfold momentConstant
  finiteness

/-- Every dyadic even moment follows from the existing native BDG
construction. The constants depend only on the common covariance cap. -/
theorem native_moment (N : FiniteScalarIto.Family F μ H (d × HaarNode))
    (p q : Parameter) (i : d) (k : ℕ) :
    (∫⁻ ω, ENNReal.ofReal
      (‖(FiniteCylindricalIto.terminalIto N.toCoordinates MatrixPredictableHaarRotation.basis).integral
          (input F μ H U hU Q hUpper hH hQ p i) ω-
        (FiniteCylindricalIto.terminalIto N.toCoordinates MatrixPredictableHaarRotation.basis).integral
          (input F μ H U hU Q hUpper hH hQ q i) ω‖^(2*2^k)) ∂μ) ≤
      momentConstant U H k*edist p q^((1/8 : ℝ)*(2^k : ℕ)) := by
  have hb := NativeScalarBDG.difference_moment_of_bracket_bound N MatrixPredictableHaarRotation.basis k _ _
    (input_bracket F μ H U hU Q hUpper hH hQ p q i)
  refine hb.trans_eq ?_
  rw [← ENNReal.ofReal_rpow_of_nonneg dist_nonneg (by norm_num : (0 : ℝ) ≤ 1/8),
    mul_pow,← ENNReal.rpow_mul_natCast,edist_dist]
  unfold momentConstant
  ring

/-- Native point observations as genuine scalar random variables. -/
def value (N : FiniteScalarIto.Family F μ H (d × HaarNode)) (p : Parameter) (i : d) : Lp ℝ 2 μ :=
  (FiniteCylindricalIto.terminalIto N.toCoordinates MatrixPredictableHaarRotation.basis).integral
    (input F μ H U hU Q hUpper hH hQ p i)

theorem input_zero (p : Parameter) (i : d) (hp : GlobalHeatParameter.time H p = 0) :
    input F μ H U hU Q hUpper hH hQ p i = 0 := by
  apply NativeInputPairing.process_ext
  have hz : (0 : Process (E := Input (d := d)) F μ H) =ᵐ[energyMeasure μ H]
      (fun _ => (0 : Input (d := d))) := ae_eq_of_ae_eq_trim
    (Lp.coeFn_zero (Input (d := d)) 2 ((energyMeasure μ H).trim (predictable_le_product F)))
  filter_upwards [MatrixPointHeatInput.input_ae F μ H hH U hU Q hUpper hQ (GlobalHeatParameter.time H p)
    (GlobalHeatParameter.time_le_horizon H p) (HeatParameterCoordinates.center p) i,hz] with z he hz
  dsimp only [input]
  rw [he,hz,hp]
  exact MatrixPointHeatInput.row_zero (by simp) (Q z) (HeatParameterCoordinates.center p) i

theorem value_zero (N : FiniteScalarIto.Family F μ H (d × HaarNode)) (p : Parameter) (i : d)
    (hp : GlobalHeatParameter.time H p = 0) : value F μ H U hU Q hUpper hH hQ N p i = 0 := by
  unfold value
  rw [input_zero F μ H U hU Q hUpper hH hQ p i hp,map_zero]

end SHEStochastic.MatrixPointJointMoments
