module

public import SHEStochastic.SmoothMildWindow
public import SHEStochastic.HaarRestartKernel

@[expose] public section
set_option autoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section

namespace SHEStochastic.SmoothMildAppend
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
  {a : ℝ → ℝ} (ha : Measurable a) {ell cap : ℝ} (hell : 0 < ell)
  (hb : ∀ z, ell ≤ a z ∧ a z ≤ cap) (Z : Ω → StateL2)

local notation "InpMeasure" => (energyMeasure μ H).trim (predictable_le_product F)

def mapInput (A : StateL2 →L[ℝ] StateL2)
    (u : Process (E := RealHaarIntegrand.Columns) F μ H) : Process (E := RealHaarIntegrand.Columns) F μ H :=
  (HilbertColumns.mapCLM A).compLpL 2 InpMeasure u

theorem mapInput_ae (A : StateL2 →L[ℝ] StateL2)
    (u : Process (E := RealHaarIntegrand.Columns) F μ H) :
    mapInput F μ H A u =ᵐ[energyMeasure μ H] fun p ↦ HilbertColumns.mapCLM A (u p) :=
  ae_eq_of_ae_eq_trim ((HilbertColumns.mapCLM A).coeFn_compLpL u)

variable {F μ H I ha hell hb Z}

def input {K h : ℝ≥0} (D : SmoothMildSegment.Data F μ H I ha hell hb Z K)
    (E : SmoothMildWindow.Data F μ H K h I ha hell hb (D.value K))
    (t : ℝ≥0) (ht : t ≤ K+h) : Process (E := RealHaarIntegrand.Columns) F μ H :=
  if htk : t ≤ K then D.input t htk else
    mapInput F μ H (RealHeat.realHeat ((t-K : ℝ≥0) : ℝ)) (D.input K le_rfl) +
      E.input (t-K) ((tsub_le_iff_right).mpr (by simpa only [add_comm] using ht))

theorem input_ae {K h : ℝ≥0} (D : SmoothMildSegment.Data F μ H I ha hell hb Z K)
    (E : SmoothMildWindow.Data F μ H K h I ha hell hb (D.value K)) (t : ℝ≥0) (ht : t ≤ K+h) :
    input D E t ht =ᵐ[energyMeasure μ H]
      SmoothMildSegment.kernel ha hell hb (AdaptedRestartGluing.value K h D.value E.value) t := by
  by_cases htk : t ≤ K
  · rw [input, dif_pos htk]
    filter_upwards [D.input_ae t htk] with p hp
    exact hp.trans (HaarRestartKernel.past ha hell hb K h D.value E.value t htk p).symm
  · rw [input, dif_neg htk]
    have hKt : K ≤ t := (lt_of_not_ge htk).le
    let A := RealHeat.realHeat ((t-K : ℝ≥0) : ℝ)
    let u := mapInput F μ H A (D.input K le_rfl)
    let w := E.input (t-K) ((tsub_le_iff_right).mpr (by simpa only [add_comm] using ht))
    have hz := (Measure.quasiMeasurePreserving_snd (μ := PredictableL2.timeMeasure H) (ν := μ)).ae (SmoothMildWindow.initial E)
    have hpK := (Measure.quasiMeasurePreserving_fst (μ := PredictableL2.timeMeasure H) (ν := μ)).ae ((PredictableL2.timeMeasure H).ae_ne K)
    filter_upwards [ae_eq_of_ae_eq_trim (Lp.coeFn_add u w), mapInput_ae F μ H A (D.input K le_rfl),
      D.input_ae K le_rfl, E.input_ae (t-K) _, hz, hpK] with p hadd hm hp he hz hpK
    change (u+w) p = _
    rw [hadd]
    change u p + w p = _
    have hu : u p = HilbertColumns.mapCLM A (D.input K le_rfl p) := hm
    have hw : w p = SHE.DeterministicItoShift.extend K h (SmoothMildSegment.kernel ha hell hb E.value (t-K)) p := he
    rw [hu, hp, hw]
    exact (HaarRestartKernel.split ha hell hb K h D.value E.value t hKt ht p hpK hz).symm

/-- Append one actual smooth mild window. Heat propagation and the SAME
integral's linear naturality give the full mild equation, rather than
an independent restart equation supplied as an extra hypothesis. -/
def append (J : StandardTerminalIto (C := RealHaarInput) (E := ℝ) F μ H)
    (hIJ : NativeObservationNaturality.StandardScalarNaturality I J)
    {K h : ℝ≥0} (D : SmoothMildSegment.Data F μ H I ha hell hb Z K)
    (E : SmoothMildWindow.Data F μ H K h I ha hell hb (D.value K)) :
    SmoothMildSegment.Data F μ H I ha hell hb Z (K+h) where
  value := AdaptedRestartGluing.value K h D.value E.value
  continuous := AdaptedRestartGluing.continuous K h D.value E.value D.continuous E.continuous
  predictable := AdaptedRestartGluing.predictable F K h D.value E.value
    (show IsStronglyPredictable F D.value from D.predictable).stronglyAdapted
    (show IsStronglyPredictable (SHE.DeterministicItoShift.filtration F K) E.value from E.predictable).stronglyAdapted
    D.continuous E.continuous
  input := input D E
  input_ae := input_ae D E
  equation := by
    intro t ht
    by_cases htk : t ≤ K
    · rw [AdaptedRestartGluing.before K h D.value E.value t htk, input, dif_pos htk]
      exact D.equation t htk
    · have hKt : K ≤ t := (lt_of_not_ge htk).le
      have hδ : t-K ≤ h := (tsub_le_iff_right).mpr (by simpa only [add_comm] using ht)
      let A := RealHeat.realHeat ((t-K : ℝ≥0) : ℝ)
      let u := mapInput F μ H A (D.input K le_rfl)
      let w := E.input (t-K) hδ
      have hc := HilbertItoNaturality.commutes F μ H I J hIJ A (D.input K le_rfl)
      have hread := AdaptedRestartGluing.future_ae μ K h D.value E.value (SmoothMildWindow.initial E)
      filter_upwards [D.equation K le_rfl, E.equation (t-K) hδ, hc, hread,
        Lp.coeFn_add (I.integral u) (I.integral w)] with ω hp he hc hr hadd
      have htread := hr t hKt
      rw [min_eq_left hδ] at htread
      rw [htread, he]
      have hheat : A (RealHeat.realHeat (K : ℝ) (Z ω)) = RealHeat.realHeat (t : ℝ) (Z ω) := by
        change (RealHeat.realHeat ((t-K : ℝ≥0) : ℝ)) (RealHeat.realHeat (K : ℝ) (Z ω)) = _
        have hs := congrArg (fun L : StateL2 →L[ℝ] StateL2 ↦ L (Z ω))
          (RealHeat.realHeat_semigroup (t-K : ℝ≥0).property K.property)
        have hh : ((t-K : ℝ≥0) : ℝ)+(K : ℝ) = (t : ℝ) := by
          rw [NNReal.coe_sub hKt]
          ring
        have hstep : A (RealHeat.realHeat (K : ℝ) (Z ω)) =
            RealHeat.realHeat (((t-K : ℝ≥0) : ℝ)+(K : ℝ)) (Z ω) := by
          convert! hs.symm using 1 <;> rfl
        exact hstep.trans (congrArg (fun r : ℝ ↦ RealHeat.realHeat r (Z ω)) hh)
      have hsum : I.integral (input D E t ht) ω = I.integral u ω + I.integral w ω := by
        rw [input, dif_neg htk, map_add]
        exact hadd
      rw [hsum]
      change A (D.value K ω) + I.integral w ω = _
      rw [hp, map_add, hheat, hc]
      change (RealHeat.realHeat (t : ℝ) (Z ω) + I.integral u ω) + I.integral w ω = _
      exact add_assoc _ _ _

end SHEStochastic.SmoothMildAppend
