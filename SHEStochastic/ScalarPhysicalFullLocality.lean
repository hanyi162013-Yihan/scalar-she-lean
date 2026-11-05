module

public import SHEStochastic.ScalarPhysicalFullInput
public import SHEStochastic.NativeRandomStopLocality
public import SHEStochastic.FiniteCylindricalParameterVersions
public import SHEStochastic.FiniteCylindricalLocality

@[expose] public section
set_option autoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section

namespace SHEStochastic.ScalarPhysicalFullLocality
open MeasureTheory Set Filter SHE SHE.PredictableL2 SHE.DyadicApproximation AddCircle
open scoped NNReal ENNReal

local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance : Fact (0 < 2*Real.pi) := ⟨by positivity⟩
local instance : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by simp⟩
local notation "Noise" => Lp ℝ 2 (haarAddCircle (T := 2*Real.pi))
local instance : MeasurableSpace Noise := borel _
local instance : BorelSpace Noise := ⟨rfl⟩
local instance : SecondCountableTopology Noise :=
  NativePhysicalState.equivalence.symm.toHomeomorph.secondCountableTopology

variable {Ω I : Type*} [MeasurableSpace Ω] [Countable I] [DecidableEq I]
  (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
  (W : ℝ≥0 → Ω → RealL2) (hW : StronglyMeasurable[F.predictable] (Function.uncurry W))
  (hc : ∀ ω,Continuous (fun t => W t ω))
  {g : ℝ → ℝ} {C β : ℝ≥0} (hg : HolderWith C β g) (hβ : 0<β) (hβ₁ : β≤1)
  (N : ℕ) (t : ℝ≥0) (ψ : ℂ →L[ℝ] ℝ) (n : ℤ)

local notation "τ" => ContinuousNormExit.exit W N
local notation "A" => {p : ℝ≥0×Ω | (p.1 : WithTop ℝ≥0)<τ p.2}
local notation "vRaw" => ScalarPhysicalStoppedEquation.row hg hβ hβ₁ W N t ψ n
local notation "wRaw" => ScalarPhysicalFullInput.row W hg hβ hβ₁ t ψ n

omit [MeasurableSpace Ω] [Countable I] [DecidableEq I] in
theorem rows (p : ℝ≥0×Ω) : vRaw p = (A).indicator wRaw p := by
  by_cases hp : p∈A
  · rw [indicator_of_mem hp]
    by_cases ht : p∈StoppedItoInputs.before (Ω := Ω) (t : ℝ)
    · rw [ScalarPhysicalStoppedEquation.row,ScalarPhysicalFullInput.row,
        indicator_of_mem (show p∈ScalarStoppedHeatFourierInput.before W N t from ⟨ht,hp⟩),
        indicator_of_mem ht]
    · rw [ScalarPhysicalStoppedEquation.row,ScalarPhysicalFullInput.row,
        indicator_of_notMem (show p∉ScalarStoppedHeatFourierInput.before W N t from fun h => ht h.1),indicator_of_notMem ht]
  · rw [indicator_of_notMem hp,ScalarPhysicalStoppedEquation.row,
      indicator_of_notMem (show p∉ScalarStoppedHeatFourierInput.before W N t from fun h => hp h.2)]

omit [Countable I] [DecidableEq I] [IsProbabilityMeasure μ] in
include hW hc in
theorem exists_cut (w : Process (E := Noise) F μ H) (hw : w=ᵐ[energyMeasure μ H] wRaw) :
    ∃ v : Process (E := Noise) F μ H,v=ᵐ[energyMeasure μ H] vRaw := by
  let : MeasurableSpace (ℝ≥0×Ω) := F.predictable
  have hA : MeasurableSet A := ScalarPredictableNormStop.predictable F W hW hc N
  have hm := (Lp.memLp w).indicator hA.nullMeasurableSet
  refine ⟨hm.toLp _,?_⟩
  filter_upwards [ae_eq_of_ae_eq_trim hm.coeFn_toLp,hw] with p hp hw
  rw [hp,rows W hg hβ hβ₁ N t ψ n]
  by_cases h : p∈A
  · simpa only [indicator_of_mem h] using hw
  · rw [indicator_of_notMem h,indicator_of_notMem h]

omit [Countable I] [DecidableEq I] [IsProbabilityMeasure μ] in
theorem stopped (u : Process (E := Noise) F μ H)
    (hu : ∀ᵐ p ∂energyMeasure μ H,p∉StoppedItoInputs.before (Ω := Ω) (t : ℝ) → u p=0) :
    StoppedItoInputs.stop F μ H t u=u := by
  apply PastItoAlgebra.eq_of_ambient_ae F μ H
  filter_upwards [StoppedItoInputs.stop_ae F μ H t u,hu] with p hs hz
  rw [hs]
  by_cases hp : p∈StoppedItoInputs.before (Ω := Ω) (t : ℝ)
  · exact indicator_of_mem hp _
  · rw [indicator_of_notMem hp,hz hp]

include hW hc in
/-- The actual stopped and full integrals agree before the state exit.
The driving Brownian family is identical on both sides. -/
theorem compare
    (P : FiniteScalarIto.Family F μ H I) (e : HilbertBasis I ℝ Noise)
    (hn : NullCompleteFiltration.ContainsNullSets F μ)
    (v w : Process (E := Noise) F μ H)
    (hv : v=ᵐ[energyMeasure μ H] vRaw)
    (hw : w=ᵐ[energyMeasure μ H] wRaw) :
    ∀ᵐ ω ∂μ,(t : WithTop ℝ≥0)<τ ω →
      (FiniteCylindricalIto.terminalIto P.toCoordinates e).integral v ω=
        (FiniteCylindricalIto.terminalIto P.toCoordinates e).integral w ω := by
  let J := FiniteCylindricalIto.terminalIto P.toCoordinates e
  have htau : IsStoppingTime F τ :=
    ContinuousNormExit.isStoppingTime W hc F (show IsStronglyPredictable F W from hW).stronglyAdapted N
  have hvT : StoppedItoInputs.stop F μ H t v=v := by
    apply stopped F μ H t v
    filter_upwards [hv] with p hp hT
    rw [hp,ScalarPhysicalStoppedEquation.row,indicator_of_notMem (show p∉ScalarStoppedHeatFourierInput.before W N t from fun h => hT h.1)]
  have hwT : StoppedItoInputs.stop F μ H t w=w := by
    apply stopped F μ H t w
    filter_upwards [hw] with p hp hT
    rw [hp,ScalarPhysicalFullInput.row,indicator_of_notMem hT]
  have hr : ∀ᵐ p ∂energyMeasure μ H,(p.1 : WithTop ℝ≥0)<τ p.2 → v p=w p := by
    filter_upwards [hv,hw] with p hv hw hp
    rw [hv,hw,rows W hg hβ hβ₁ N t ψ n,indicator_of_mem (show p∈A from hp)]
  exact (NativeRandomStopLocality.integral_eq_before F μ H J
    (FiniteCylindricalIto.pastLocality P e) (FiniteCylindricalIto.continuousStoppedVersions P e)
    hn v w t hvT hwT τ htau hr).mono (fun _ h ht => h ht.le)

end SHEStochastic.ScalarPhysicalFullLocality
