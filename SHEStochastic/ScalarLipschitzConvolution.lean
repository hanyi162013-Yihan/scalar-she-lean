module

public import SHEStochastic.ScalarLipschitzKernelBounds
public import SHEStochastic.NativeHilbertBDG
public import SHEStochastic.NativeNoiseEquivalence
public import SHEStochastic.ScalarGrowingFourierInput

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section

namespace SHEStochastic.ScalarLipschitzConvolution
open MeasureTheory Set SHE SHE.PredictableL2 SHE.StoppedFourier SHE.DyadicApproximation SHE.FiniteHaar AddCircle
open ScalarLipschitzHeatColumn ScalarLipschitzHeatColumns ScalarLipschitzKernelBounds
open scoped NNReal ENNReal

local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance : Fact (0 < 2*Real.pi) := ⟨by positivity⟩
local instance : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by simp⟩
local notation "ν" => haarAddCircle (T := 2*Real.pi)
local notation "Noise" => Lp ℝ 2 ν
local notation "φ" => NativeFourierHeatCoordinate.coordinate
local notation "w" => NativeFourierHeatCoordinate.weight
local instance : SecondCountableTopology CircleHeat.CircleL2 :=
  (_root_.fourierBasis (T := (1 : ℝ))).repr.toHomeomorph.secondCountableTopology
local instance : SecondCountableTopology RealL2 := realCircleIdentification.toHomeomorph.secondCountableTopology
local instance : MeasurableSpace RealL2 := borel _
local instance : BorelSpace RealL2 := ⟨rfl⟩
local instance : MeasurableSpace Noise := borel _
local instance : BorelSpace Noise := ⟨rfl⟩
local instance : SecondCountableTopology Noise :=
  NativePhysicalState.equivalence.symm.toHomeomorph.secondCountableTopology

variable {Ω I : Type*} [MeasurableSpace Ω] [Countable I] [DecidableEq I]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {μ : Measure Ω} [IsProbabilityMeasure μ] {H : ℝ≥0}
  (e : HilbertBasis I ℝ Noise)

local notation "Col" => HilbertColumns.Space I RealL2
local instance : MeasurableSpace Col := borel _
local instance : BorelSpace Col := ⟨rfl⟩

/-- Use the same Brownian coordinates as the scalar weak equation. -/
def ito (P : FiniteScalarIto.Family F μ H I) :
    StandardTerminalIto (C := Col) (E := RealL2) F μ H :=
  HilbertTerminalIto.terminalIto F μ H
    (NativeNoiseEquivalence.basis NativePhysicalState.equivalence e)
    (restrictNoise (FiniteCylindricalIto.terminalIto P.toCoordinates e) e.repr.symm.toLinearIsometry)

theorem bdg (P : FiniteScalarIto.Family F μ H I) :
    StandardTerminalBDGPower 8 (ito e P) (NativeScalarBDG.constant 3) := by
  intro u
  exact NativeHilbertBDG.power_two P e e.repr.symm.toLinearIsometry
    (NativeNoiseEquivalence.basis NativePhysicalState.equivalence e) 3 u

variable {g : ℝ → ℝ} {C : ℝ≥0} (hg : HolderWith C 1 g)
  (U : ℝ≥0 → Ω → RealL2)
  (hU : StronglyMeasurable[F.predictable] (Function.uncurry U))

def raw (t : ℝ≥0) (p : ℝ≥0 × Ω) : Col :=
  kernel e ((t : ℝ)-(p.1 : ℝ)) (coefficient hg (U p.1 p.2))

omit [DecidableEq I] in
include hU in
theorem raw_predictable (t : ℝ≥0) : StronglyMeasurable[F.predictable] (raw e hg U t) := by
  let : MeasurableSpace (ℝ≥0×Ω) := F.predictable
  have ht : Measurable (fun p : ℝ≥0 × Ω => (t : ℝ)-(p.1 : ℝ)) :=
    measurable_const.sub (NNReal.continuous_coe.measurable.comp (PredictableClock.time_measurable F))
  have ha := ((coefficient_continuous hg).comp_stronglyMeasurable hU).measurable
  exact ((kernel_measurable e).comp (ht.prodMk ha)).stronglyMeasurable

omit [DecidableEq I] in
include hU in
theorem raw_measurable (t : ℝ≥0) : Measurable (raw e hg U t) :=
  ((raw_predictable e hg U hU t).mono (predictable_le_product F)).measurable

omit [MeasurableSpace Ω] [Countable I] [DecidableEq I] in
theorem raw_zero (t : ℝ≥0) {p : ℝ≥0 × Ω} (hp : t≤p.1) : raw e hg U t p=0 :=
  kernel_zero e (sub_nonpos.mpr (by exact_mod_cast hp)) _

omit [IsProbabilityMeasure μ] [DecidableEq I] in
include hU in
theorem memLp (t : ℝ≥0)
    (hE : Integrable (fun p => ‖raw e hg U t p‖^2) (energyMeasure μ H)) :
    @MemLp _ _ F.predictable _ _ (raw e hg U t) 2 ((energyMeasure μ H).trim (predictable_le_product F)) := by
  have hm := raw_predictable e hg U hU t
  have ha := (hm.mono (predictable_le_product F)).aestronglyMeasurable (μ := energyMeasure μ H)
  have h := (memLp_two_iff_integrable_sq_norm ha).mpr hE
  exact (eLpNorm_trim (predictable_le_product F) hm).trans_lt h

def input (t : ℝ≥0)
    (hE : Integrable (fun p => ‖raw e hg U t p‖^2) (energyMeasure μ H)) :
    Process (E := Col) F μ H :=
  (memLp e hg U hU t hE).toLp (raw e hg U t)

omit [IsProbabilityMeasure μ] [DecidableEq I] in
theorem input_ae (t : ℝ≥0)
    (hE : Integrable (fun p => ‖raw e hg U t p‖^2) (energyMeasure μ H)) :
    input e hg U hU t hE =ᵐ[energyMeasure μ H] raw e hg U t :=
  ae_eq_of_ae_eq_trim (memLp e hg U hU t hE).coeFn_toLp

theorem adapted (P : FiniteScalarIto.Family F μ H I)
    (hn : NullCompleteFiltration.ContainsNullSets F μ) (t : ℝ≥0)
    (hE : Integrable (fun p => ‖raw e hg U t p‖^2) (energyMeasure μ H)) :
    StronglyMeasurable[F t] ((ito e P).integral (input e hg U hU t hE) : Ω → RealL2) := by
  obtain ⟨Z,hZ,hZeq⟩ := (ito e P).adapted t (input e hg U hU t hE)
    ((input_ae e hg U hU t hE).mono (fun p hp ht => hp.trans (raw_zero e hg U t ht.le)))
  exact NullCompleteFiltration.stronglyMeasurable_congr F μ hn t hZ hZeq

omit [MeasurableSpace Ω] [Countable I] [DecidableEq I] in
/-- The actual heat input row obtained by testing the Hilbert integral.
This identity uses the original cylindrical Brownian coordinates. -/
theorem raw_row (t : ℝ≥0) (p : ℝ≥0×Ω) (ψ : ℂ →L[ℝ] ℝ) (n : ℤ) :
    e.repr.symm ((HilbertColumns.mapCLM (φ ψ n)) (raw e hg U t p)) =
      (if p.1<t then Real.exp (-((t : ℝ)-(p.1 : ℝ))*(n : ℝ)^2) else 0) •
        StateNoiseCovariance.row ν zero_lt_one le_rfl hg (w ψ n) (NativePhysicalState.push (U p.1 p.2)) := by
  by_cases ht : p.1<t
  · rw [ite_eq_left ht]
    apply e.repr.injective
    rw [LinearIsometryEquiv.apply_symm_apply,map_smul]
    apply lp.ext
    funext i
    change φ ψ n (column ((t : ℝ)-(p.1 : ℝ)) (coefficient hg (U p.1 p.2)) (e i)) =
      Real.exp (-((t : ℝ)-(p.1 : ℝ))*(n : ℝ)^2) *
        e.repr (StateNoiseCovariance.row ν zero_lt_one le_rfl hg (w ψ n) (NativePhysicalState.push (U p.1 p.2))) i
    rw [column_mode (sub_pos.mpr (by exact_mod_cast ht)),weighted_coefficient,
      HilbertBasis.repr_apply_apply,real_inner_comm]
  · rw [ite_eq_right ht,raw_zero e hg U t (le_of_not_gt ht),map_zero,map_zero,zero_smul]

end SHEStochastic.ScalarLipschitzConvolution
