module

public import SHEStochastic.GlobalClockedRandomMildExistence
public import SHEStochastic.GlobalNativeHaarMildEquation
public import SHEStochastic.NativeHeatNaturality

@[expose] public section
set_option autoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1000000
noncomputable section

namespace SHEStochastic.GlobalNativeSmoothWeakExistence
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

variable {Ω ι κ η : Type*} [MeasurableSpace Ω] [Countable ι] [DecidableEq ι]
  [Countable κ] [Countable η] [DecidableEq η]
  (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
  (P : FiniteScalarIto.Family F μ H ι) (e : HilbertBasis ι ℝ RealHaarInput)
  (b : HilbertBasis κ ℝ RealL2)
  (q : HilbertBasis η ℝ (Lp ℝ 2 (haarAddCircle (T := 2 * Real.pi))))

local notation "FN" => PredictableTimeDilation.filtration F
  (PredictableTimeDilation.clock NativeClock.rate NativeClock.rate_pos)

include P e b in
/-- Actual smooth bounded scalar weak existence with arbitrary random
L2 initial data. The initial law, physical heat clock, pointwise scalar
coefficient and native Brownian integration are all realized by the
constructed solution. No existence or representation axiom is supplied. -/
theorem exists_solution (hpos : 0 < H)
    (hnull : NullCompleteFiltration.ContainsNullSets F μ)
    {a G : ℝ → ℝ} (ha : Measurable a) {ell cap K α : ℝ}
    (hell : 0 < ell) (hb : ∀ z, ell ≤ a z ∧ a z ≤ cap)
    (hα : 0 < α) (hK : 0 ≤ K) (hholder : ∀ z w, |a z-a w| ≤ K*|z-w|^α)
    {L : ℝ≥0} (hLip : LipschitzWith L (fun z ↦ (a z : ℂ)))
    (hsquare : ∀ z, a z = (G z)^2) (hGpos : ∀ z, 0 ≤ G z)
    {C β : ℝ≥0} (hG : HolderWith C β G) (hβ : 0 < β) (hβ1 : β < 1)
    (Z : Ω → RealL2) (hZ₀ : StronglyMeasurable[F 0] Z) (hZ : MemLp Z 2 μ) :
    ∃ W : ℝ≥0 → Ω → RealL2, (∀ sample, Continuous (fun t ↦ W t sample)) ∧
      ∃ hW : StronglyMeasurable[(FN).predictable] (Function.uncurry W),
        W 0 =ᵐ[μ] Z ∧ ∃ Q : FiniteScalarIto.Family FN μ (NativeClock.rate*H) η,
          UnboundedGlobalNativeEquation.RandomEquation FN μ (NativeClock.rate*H) W hW hG hβ hβ1 Q q Z := by
  obtain ⟨W, hWc, hWp, hf, v, hv, hmild⟩ := GlobalClockedRandomMildExistence.exists_mild F μ H P e b
    hnull ha hell hb hα hK hholder hLip Z hZ₀ hZ
  obtain ⟨R, hR⟩ := NativeTimeDilatedFamily.exists_family F μ NativeClock.rate NativeClock.rate_pos H P e hnull
  let I := PredictableTimeDilation.integral F μ NativeClock.rate NativeClock.rate_pos H
    (NativeSmoothRandomMildExistence.integral F μ H P e
      (LinearIsometry.id : RealHaarInput →ₗᵢ[ℝ] RealHaarInput) b)
  have hIJ : NativeObservationNaturality.StandardScalarNaturality I
      (FiniteCylindricalIto.terminalIto R.toCoordinates e) := by
    constructor
    intro A u
    exact ((NativeHeatNaturality.clocked F μ H P e b NativeClock.rate NativeClock.rate_pos).commutes A u).trans
      (hR _).symm
  have hv0 : v 0 = 0 := by
    apply PastItoAlgebra.eq_of_ambient_ae
    filter_upwards [hv 0 zero_le, ae_eq_of_ae_eq_trim
      (Lp.coeFn_zero RealHaarIntegrand.Columns 2
        ((energyMeasure μ (NativeClock.rate*H)).trim (predictable_le_product FN)))] with p hp hz
    rw [hp, NativeHeatObservation.kernel_zero hell (by simp only [NNReal.coe_zero, zero_sub]; exact neg_nonpos.mpr p.1.2)]
    exact hz.symm
  have hInitial : W 0 =ᵐ[μ] Z := by
    have h0 := hmild 0 zero_le
    rw [hv0, map_zero] at h0
    filter_upwards [h0, Lp.coeFn_zero RealL2 2 μ] with sample hs hz
    change W 0 sample = NativeHeatObservation.heat 0 (Z sample) + (0 : Lp RealL2 2 μ) sample at hs
    rw [hz] at hs
    simpa only [NNReal.coe_zero, NativeHeatObservation.heat, zero_div, RealHeat.realHeat_zero,
      ContinuousLinearMap.id_apply, Pi.zero_apply, add_zero] using hs
  obtain ⟨Q, hQ⟩ := GlobalNativeHaarMildEquation.exists_physical_equation FN μ (NativeClock.rate*H) R e q
    (PredictableTimeDilation.containsNullSets F _ μ hnull) ha hell hb hsquare hGpos hG hβ hβ1
    W hWp hWc hf I hIJ Z v hv hmild
  exact ⟨W, hWc, hWp, hInitial, Q, hQ⟩

end SHEStochastic.GlobalNativeSmoothWeakExistence
