module

public import SHEStochastic.UnboundedL2Localization
public import SHEStochastic.UnboundedFiniteHorizonInput
public import SHEStochastic.NativeRandomStopLocality
public import SHEStochastic.FiniteCylindricalParameterVersions

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHEStochastic.UnboundedLocalizedHeatRows
open MeasureTheory SHE SHE.PredictableL2 AddCircle
open scoped NNReal ENNReal

local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

variable {Ω E V : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]
  (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›)
  (U : ℝ≥0 × Ω → Lp E 2 (haarAddCircle (T := 2 * Real.pi)))
  (hU : StronglyMeasurable[F.predictable] U)
  {G : E → V} {C β : ℝ≥0} (hG : HolderWith C β G) (hβ : 0 < β) (hβ1 : β < 1)
  (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)

/-- The original heat row after projecting only the L2 state. All
integrability bounds come from that projection's actual norm bound. -/
def globalRow (R T : ℝ≥0) (hTH : T ≤ H) (a : StoppedFourier.HeatCircle) :
    Process (E := Lp V 2 (haarAddCircle (T := 2 * Real.pi))) F μ H :=
  UnboundedFiniteHorizonInput.input F (UnboundedL2Localization.state U R)
    (UnboundedL2Localization.predictable F U hU R) hG hβ hβ1 μ H T hTH a
    (UnboundedL2Localization.history_bound U μ H R)

theorem globalRow_ae (R T : ℝ≥0) (hTH : T ≤ H) (a : StoppedFourier.HeatCircle) :
    globalRow F U hU hG hβ hβ1 μ H R T hTH a =ᵐ[energyMeasure μ H]
      UnboundedHeatFamily.family F (UnboundedL2Localization.state U R)
        (UnboundedL2Localization.predictable F U hU R) hG hβ hβ1 T a :=
  UnboundedFiniteHorizonInput.input_ae F (UnboundedL2Localization.state U R)
    (UnboundedL2Localization.predictable F U hU R) hG hβ hβ1 μ H T hTH a
    (UnboundedL2Localization.history_bound U μ H R)

/-- Existing unit-time row interface, now a specialization of the
same globally integrable native row. -/
def row (R T : ℝ≥0) (hTH : T≤H) (hT : (T:ℝ)≤1) (a : StoppedFourier.HeatCircle) :
    Process (E := Lp V 2 (haarAddCircle (T := 2*Real.pi))) F μ H :=
  UnboundedHeatFamily.input F (UnboundedL2Localization.state U R)
    (UnboundedL2Localization.predictable F U hU R) hG hβ hβ1 μ H T hTH hT a
    (UnboundedL2Localization.history_bound U μ H R)

theorem row_ae (R T : ℝ≥0) (hTH : T≤H) (hT : (T:ℝ)≤1) (a : StoppedFourier.HeatCircle) :
    row F U hU hG hβ hβ1 μ H R T hTH hT a=ᵐ[energyMeasure μ H]
      UnboundedHeatFamily.family F (UnboundedL2Localization.state U R)
        (UnboundedL2Localization.predictable F U hU R) hG hβ hβ1 T a :=
  globalRow_ae F U hU hG hβ hβ1 μ H R T hTH a

theorem global_agree_before_exit (hc : ∀ ω, Continuous (fun t ↦ U (t, ω)))
    (N : ℕ) (R S T : ℝ≥0) (hNR : (N : ℝ) ≤ R) (hNS : (N : ℝ) ≤ S)
    (hTH : T ≤ H) (a : StoppedFourier.HeatCircle) :
    ∀ᵐ p ∂energyMeasure μ H,
      (p.1 : WithTop ℝ≥0) < ContinuousNormExit.exit (fun t ω ↦ U (t, ω)) N p.2 →
        globalRow F U hU hG hβ hβ1 μ H R T hTH a p =
          globalRow F U hU hG hβ hβ1 μ H S T hTH a p := by
  filter_upwards [globalRow_ae F U hU hG hβ hβ1 μ H R T hTH a,
    globalRow_ae F U hU hG hβ hβ1 μ H S T hTH a] with p hR hS hbefore
  rw [hR, hS]
  apply UnboundedHeatFamily.state_congr
  have hb := (ContinuousNormExit.before_bound (fun t ω ↦ U (t, ω)) hc N p.1 p.2 hbefore).le
  exact (UnboundedL2Localization.agrees U R (hb.trans hNR)).trans
    (UnboundedL2Localization.agrees U S (hb.trans hNS)).symm

theorem agree_before_exit (hc : ∀ ω, Continuous (fun t ↦ U (t, ω)))
    (N : ℕ) (R S T : ℝ≥0) (hNR : (N : ℝ) ≤ R) (hNS : (N : ℝ) ≤ S)
    (hTH : T ≤ H) (hT : (T : ℝ) ≤ 1) (a : StoppedFourier.HeatCircle) :
    ∀ᵐ p ∂energyMeasure μ H,
      (p.1 : WithTop ℝ≥0) < ContinuousNormExit.exit (fun t ω ↦ U (t, ω)) N p.2 →
        row F U hU hG hβ hβ1 μ H R T hTH hT a p =
          row F U hU hG hβ hβ1 μ H S T hTH hT a p :=
  global_agree_before_exit F U hU hG hβ hβ1 μ H hc N R S T hNR hNS hTH a

theorem global_native_eq_before (hc : ∀ ω, Continuous (fun t ↦ U (t, ω)))
    (N : ℕ) (R S T : ℝ≥0) (hNR : (N : ℝ) ≤ R) (hNS : (N : ℝ) ≤ S)
    (hTH : T ≤ H) (a : StoppedFourier.HeatCircle)
    {ι : Type*} [Countable ι] [DecidableEq ι]
    (P : FiniteScalarIto.Family F μ H ι)
    (e : HilbertBasis ι ℝ (Lp V 2 (haarAddCircle (T := 2 * Real.pi))))
    (hnull : NullCompleteFiltration.ContainsNullSets F μ) :
    ∀ᵐ ω ∂μ, (T : WithTop ℝ≥0) ≤ ContinuousNormExit.exit (fun t ω ↦ U (t, ω)) N ω →
      (FiniteCylindricalIto.terminalIto P.toCoordinates e).integral
        (globalRow F U hU hG hβ hβ1 μ H R T hTH a) ω =
      (FiniteCylindricalIto.terminalIto P.toCoordinates e).integral
        (globalRow F U hU hG hβ hβ1 μ H S T hTH a) ω := by
  letI : MeasurableSpace (Lp V 2 (haarAddCircle (T := 2 * Real.pi))) := borel _
  letI : BorelSpace (Lp V 2 (haarAddCircle (T := 2 * Real.pi))) := ⟨rfl⟩
  letI : SecondCountableTopology (Lp V 2 (haarAddCircle (T := 2 * Real.pi))) :=
    e.repr.toHomeomorph.secondCountableTopology
  apply NativeRandomStopLocality.integral_eq_before F μ H
    (FiniteCylindricalIto.terminalIto P.toCoordinates e) (FiniteCylindricalIto.pastLocality P e)
    (FiniteCylindricalIto.continuousStoppedVersions P e) hnull
    (globalRow F U hU hG hβ hβ1 μ H R T hTH a)
    (globalRow F U hU hG hβ hβ1 μ H S T hTH a) T
  · exact UnboundedFiniteHorizonInput.input_stop F _ _ hG hβ hβ1 μ H T hTH a _
  · exact UnboundedFiniteHorizonInput.input_stop F _ _ hG hβ hβ1 μ H T hTH a _
  · exact UnboundedL2Localization.exit_stopping F U hU hc N
  · exact global_agree_before_exit F U hU hG hβ hβ1 μ H hc N R S T hNR hNS hTH a

theorem native_eq_before (hc : ∀ ω, Continuous (fun t ↦ U (t, ω)))
    (N : ℕ) (R S T : ℝ≥0) (hNR : (N : ℝ) ≤ R) (hNS : (N : ℝ) ≤ S)
    (hTH : T ≤ H) (hT : (T : ℝ) ≤ 1) (a : StoppedFourier.HeatCircle)
    {ι : Type*} [Countable ι] [DecidableEq ι]
    (P : FiniteScalarIto.Family F μ H ι)
    (e : HilbertBasis ι ℝ (Lp V 2 (haarAddCircle (T := 2 * Real.pi))))
    (hnull : NullCompleteFiltration.ContainsNullSets F μ) :
    ∀ᵐ ω ∂μ, (T : WithTop ℝ≥0) ≤ ContinuousNormExit.exit (fun t ω ↦ U (t, ω)) N ω →
      (FiniteCylindricalIto.terminalIto P.toCoordinates e).integral
        (row F U hU hG hβ hβ1 μ H R T hTH hT a) ω =
      (FiniteCylindricalIto.terminalIto P.toCoordinates e).integral
        (row F U hU hG hβ hβ1 μ H S T hTH hT a) ω :=
  global_native_eq_before F U hU hG hβ hβ1 μ H hc N R S T hNR hNS hTH a P e hnull

end SHEStochastic.UnboundedLocalizedHeatRows
