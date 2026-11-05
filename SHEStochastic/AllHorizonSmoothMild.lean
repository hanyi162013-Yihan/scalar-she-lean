module

public import SHEStochastic.SmoothMildAppend
public import SHEStochastic.NativeHeatNaturality

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
noncomputable section

namespace SHEStochastic.AllHorizonSmoothMild
open MeasureTheory SHE SHE.PredictableL2 SHE.LowBands SHE.FiniteHaar
open scoped NNReal ENNReal

local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨by simp⟩
local instance : MeasurableSpace StateL2 := borel _
local instance : BorelSpace StateL2 := ⟨rfl⟩
local instance : MeasurableSpace RealHaarIntegrand.Columns := borel _
local instance : BorelSpace RealHaarIntegrand.Columns := ⟨rfl⟩
local instance : MeasurableSpace RealHaarInput := borel _
local instance : BorelSpace RealHaarInput := ⟨rfl⟩

variable {Ω : Type*} [MeasurableSpace Ω]
  (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
  (I : StandardTerminalIto (C := RealHaarIntegrand.Columns) (E := StateL2) F μ H)
  (J : StandardTerminalIto (C := RealHaarInput) (E := ℝ) F μ H)
  (hIJ : NativeObservationNaturality.StandardScalarNaturality I J)
  (B : ℝ≥0) (hBDG : StandardTerminalBDG16 I B)
  (hnull : NullCompleteFiltration.ContainsNullSets F μ)
  {a : ℝ → ℝ} (ha : Measurable a) {ell cap K β : ℝ} (hell : 0 < ell)
  (hb : ∀ z, ell ≤ a z ∧ a z ≤ cap)
  (hβ : 0 < β) (hK : 0 ≤ K) (hholder : ∀ z w, |a z-a w| ≤ K*|z-w|^β)
  {L : ℝ≥0} (hLip : LipschitzWith L (fun z ↦ (a z : ℂ)))
  (Z : Ω → StateL2) (hZ₀ : StronglyMeasurable[F 0] Z) (hZ : MemLp Z 2 μ)

include hIJ hBDG hnull hβ hK hholder hLip hZ₀ hZ in
/-- Actual smooth mild existence on every finite horizon, obtained by
restarting the existing Picard construction on unit windows. Each input
and every window equation belongs to the SAME supplied global integral. -/
theorem exists_data : Nonempty (SmoothMildSegment.Data F μ H I ha hell hb Z H) := by
  have hex : ∀ n : ℕ, ∀ T : ℝ≥0, T ≤ H → T ≤ n →
      Nonempty (SmoothMildSegment.Data F μ H I ha hell hb Z T) := by
    intro n
    induction n with
    | zero =>
      intro T hTH hT
      have hz : T = 0 := le_antisymm (by simpa only [Nat.cast_zero] using hT) zero_le
      subst T
      exact ⟨SmoothMildSegment.zero hZ₀⟩
    | succ n ih =>
      intro T hTH hT
      by_cases hn : T ≤ n
      · exact ih T hTH hn
      · have hnT : (n : ℝ≥0) ≤ T := (lt_of_not_ge hn).le
        obtain ⟨D⟩ := ih n (hnT.trans hTH) le_rfl
        have hs : (n : ℝ≥0)+(T-n) = T := add_tsub_cancel_of_le hnT
        have hh : (T-n : ℝ≥0) ≤ 1 := (tsub_le_iff_right).mpr (by
          simpa only [Nat.cast_add, Nat.cast_one, add_comm] using hT)
        have hpos : 0 < T-n := tsub_pos_iff_lt.mpr (lt_of_not_ge hn)
        have hinit : StronglyMeasurable[F n] (D.value n) :=
          (show IsStronglyPredictable F D.value from D.predictable).stronglyAdapted n
        obtain ⟨E⟩ := SmoothMildWindow.exists_data (F := F) (μ := μ) (H := H) (v := n) (h := T-n)
          (I := I) (ha := ha) (hell := hell) (hb := hb) (Z := D.value n)
          (by rw [hs]; exact hTH) hh hpos B hBDG hnull hβ hK hholder hLip hinit
          (SmoothMildSegment.memLp D hZ n le_rfl)
        have hw : Nonempty (SmoothMildSegment.Data F μ H I ha hell hb Z ((n : ℝ≥0)+(T-n))) :=
          ⟨SmoothMildAppend.append J hIJ D E⟩
        simpa only [hs] using hw
  obtain ⟨n, hn⟩ := exists_nat_ge (H : ℝ)
  exact hex n H le_rfl (by exact_mod_cast hn)

include hnull hβ hK hholder hLip hZ₀ hZ in
/-- Native version: the required Hilbert BDG and linear naturality are
constructed from the actual Brownian family and countable Hilbert lift. -/
theorem native {ι κ : Type*} [Countable ι] [DecidableEq ι] [Countable κ]
    (P : FiniteScalarIto.Family F μ H ι) (e : HilbertBasis ι ℝ RealHaarInput)
    (b : HilbertBasis κ ℝ StateL2) :
    Nonempty (SmoothMildSegment.Data F μ H
      (NativeSmoothRandomMildExistence.integral F μ H P e
        (LinearIsometry.id : RealHaarInput →ₗᵢ[ℝ] RealHaarInput) b) ha hell hb Z H) := by
  exact exists_data F μ H _ _ (NativeHeatNaturality.scalarNaturality F μ H P e b)
    (NativeScalarBDG.constant 3)
    (NativeHilbertBDG.hilbertBDG16 P e (LinearIsometry.id : RealHaarInput →ₗᵢ[ℝ] RealHaarInput) b)
    hnull ha hell hb hβ hK hholder hLip Z hZ₀ hZ

end SHEStochastic.AllHorizonSmoothMild
