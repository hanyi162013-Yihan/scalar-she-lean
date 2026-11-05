module

public import SHEStochastic.PhysicalRootLocalization
public import SHEStochastic.NativeRandomStopLocality
public import SHEStochastic.NoiseRestriction
public import SHE.NativeObservationNaturality

@[expose] public section
set_option autoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1000000
noncomputable section

namespace SHEStochastic.NativeHaarMildEquation
open MeasureTheory SHE SHE.PredictableL2 SHE.FiniteHaar SHE.DyadicApproximation SHE.StoppedFourier AddCircle
open scoped NNReal ENNReal

local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
local instance : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨by simp⟩
local instance : MeasurableSpace RealHaarInput := borel _
local instance : BorelSpace RealHaarInput := ⟨rfl⟩
local instance : MeasurableSpace RealL2 := borel _
local instance : BorelSpace RealL2 := ⟨rfl⟩
local instance : MeasurableSpace RealHaarIntegrand.Columns := borel _
local instance : BorelSpace RealHaarIntegrand.Columns := ⟨rfl⟩
local instance : MeasurableSpace (Lp ℝ 2 (haarAddCircle (T := 2 * Real.pi))) := borel _
local instance : BorelSpace (Lp ℝ 2 (haarAddCircle (T := 2 * Real.pi))) := ⟨rfl⟩

variable {Ω ι κ : Type*} [MeasurableSpace Ω] [Countable ι] [DecidableEq ι] [Countable κ] [DecidableEq κ]
  (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
  (P : FiniteScalarIto.Family F μ H ι) (e : HilbertBasis ι ℝ RealHaarInput)
  (b : HilbertBasis κ ℝ (Lp ℝ 2 (haarAddCircle (T := 2 * Real.pi))))
  (hnull : NullCompleteFiltration.ContainsNullSets F μ)
  {a G : ℝ → ℝ} (ha : Measurable a) {ell cap : ℝ}
  (hell : 0 < ell) (hb : ∀ z, ell ≤ a z ∧ a z ≤ cap)
  (hsquare : ∀ z, a z = (G z)^2) (hGpos : ∀ z, 0 ≤ G z)
  {C β : ℝ≥0} (hG : HolderWith C β G) (hβ : 0 < β) (hβ1 : β < 1)
  (W : ℝ≥0 → Ω → RealL2) (hW : StronglyMeasurable[F.predictable] (Function.uncurry W))
  (hcW : ∀ sample, Continuous (fun t ↦ W t sample))
  (hf : StronglyMeasurable[F.predictable] (ContinuousHeatMild.coefficientFunction ha hell hb W))

local notation "f" => ContinuousHeatMild.coefficientFunction ha hell hb W
local notation "hcap" => hell.le.trans ((hb 0).1.trans (hb 0).2)
local notation "J" => FiniteCylindricalIto.terminalIto P.toCoordinates e

include hnull hsquare hGpos hcW hf in
/-- A constructed native Haar mild solution is an actual weak solution
with the literal physical scalar coefficient and a constructed Brownian
family. Random initial data are retained; localization is proved with
the existing native random-stop theorem. -/
theorem exists_physical_equation
    (I : StandardTerminalIto (C := RealHaarIntegrand.Columns) (E := RealL2) F μ H)
    (hIJ : NativeObservationNaturality.StandardScalarNaturality I J)
    (Z : Ω → RealL2) (v : ℝ≥0 → Process (E := RealHaarIntegrand.Columns) F μ H)
    (hv : ∀ t : ℝ≥0, t ≤ H → v t =ᵐ[energyMeasure μ H]
      fun p ↦ NativeHeatObservation.kernel ell cap hell ((t : ℝ)-(p.1 : ℝ), f p))
    (hmild : ∀ t : ℝ≥0, t ≤ H → W t =ᵐ[μ] fun sample ↦
      NativeHeatObservation.heat t (Z sample) + I.integral (v t) sample) :
    ∃ Q : FiniteScalarIto.Family F μ H κ,
      UnboundedNativeHeatEquation.RandomEquation F μ H W hW hG hβ hβ1 Q b Z := by
  obtain ⟨Q, hQ⟩ := NativePhysicalInnovation.exists_family F μ H hell f hf
    (LinearIsometry.id : RealHaarInput →ₗᵢ[ℝ] RealHaarInput) P e b hnull
  have hJ (u : Process (E := RealHaarInput) F μ H) :
      (FiniteCylindricalIto.terminalIto Q.toCoordinates b).integral
        (NativePhysicalObservationInput.decode F μ H hell f hf u) = (J).integral u := by
    rw [hQ, NativePhysicalObservationInput.encode_decode]
    exact restrictNoise_id J u
  refine ⟨Q, ?_⟩
  intro N T δ hTH hT1 hδ hTD hTD1 x
  have hgap : (T : ℝ) < (T+δ : ℝ≥0) := by exact_mod_cast lt_add_of_pos_right T hδ
  let u := NativePhysicalObservationInput.decode F μ H hell f hf
    (NativeObservationProcess.process F μ H hell hcap f hf hgap x)
  let w := StoppedItoInputs.stop F μ H T
    (UnboundedNativeHeatEquation.row F μ H W hW hG hβ hβ1 N (T+δ) hTD hTD1 x)
  have hu : StoppedItoInputs.stop F μ H T u = u := by
    apply PastItoAlgebra.eq_of_ambient_ae
    filter_upwards [StoppedItoInputs.stop_ae F μ H T u,
      NativePhysicalObservationInput.observation_ae F μ H hell f hf hcap hgap x] with p hp hu
    change u p = _ at hu
    rw [hp]
    by_cases ht : (p.1 : ℝ) < T
    · exact Set.indicator_of_mem (show p ∈ StoppedItoInputs.before (Ω := Ω) T from ht) _
    · rw [Set.indicator_of_notMem (show p ∉ StoppedItoInputs.before (Ω := Ω) T from ht), hu, ite_eq_right ht]
  have hw : StoppedItoInputs.stop F μ H T w = w := by
    exact (StoppedInputAlgebra.stop_stop F μ H T T _).trans (by rw [min_self])
  have he := NativeRandomStopLocality.integral_eq_before F μ H
    (FiniteCylindricalIto.terminalIto Q.toCoordinates b) (FiniteCylindricalIto.pastLocality Q b)
    (FiniteCylindricalIto.continuousStoppedVersions Q b) hnull u w T hu hw
    (UnboundedNativeHeatEquation.exit W N) (UnboundedNativeHeatEquation.exit_stopping F W hW hcW N)
    (PhysicalRootLocalization.agrees_before_exit F μ H ha hell hb hsquare hGpos hG hβ hβ1
      W hW hcW hf N (T+δ) T hgap hTD hTD1 x)
  have ho := NativeObservationNaturality.observe_terminal_integral I J hIJ hell hcap f hf hgap x (v T) (hv T hTH)
  have hage : ((T+δ : ℝ≥0) : ℝ)-(T : ℝ) = (δ : ℝ) := by push_cast; ring
  rw [hage] at ho
  filter_upwards [hmild T hTH, ho, he] with sample hm ho he hbefore
  rw [hm, map_add]
  have hheat := NativeHeatObservation.functional_heat (show (0 : ℝ) < δ from hδ)
    (show (0 : ℝ) ≤ T from T.2) x (Z sample)
  rw [hheat, ho]
  have hsum : (δ : ℝ)+(T : ℝ) = ((T+δ : ℝ≥0) : ℝ) := by push_cast; ring
  rw [hsum]
  congr 1
  exact (congrArg (fun z : Lp ℝ 2 μ ↦ z sample) (hJ _)).symm.trans (he hbefore.le)

end SHEStochastic.NativeHaarMildEquation
