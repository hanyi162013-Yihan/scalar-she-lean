module

public import SHE.FiniteItoGradientMajorant
public import SHE.FiniteItoPastNoise
public import SHE.PastParameterItoIdentity

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
namespace SHE.FiniteItoGradientFamily
open Set MeasureTheory PredictableL2 FiniteItoNoise Filter Topology
open scoped NNReal ENNReal
variable {Ω X C : Type*} [MeasurableSpace Ω]
variable [PseudoMetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [NormedAddCommGroup C] [InnerProductSpace ℝ C]
variable [MeasurableSpace C] [BorelSpace C] [SecondCountableTopology C]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) (H : ℝ≥0)
variable {n : ℕ} (Y : ℝ≥0×Ω→WordRecursion.State n)
variable (hY : StronglyMeasurable[𝓕.predictable] Y) (R : Fin n→Process (E:=C) 𝓕 μ H)
variable (G : X→ℝ→WordRecursion.State n→ℝ)
variable (hc : Continuous (fun p : X×(ℝ×WordRecursion.State n)=>fderiv ℝ (G p.1 p.2.1) p.2.2))
variable (c : ℝ≥0)

/-- The actual bounded-gradient row family, stopped before the chosen
prefix. The random test parameter will be selected strictly after v. -/
def raw (x : X) (p : ℝ≥0×Ω) : C :=
  if p.1<c then gradientRow 𝓕 μ H Y R (G x) p else 0

include hY hc in
theorem measurable_raw : @Measurable (X×(ℝ≥0×Ω)) C
    ((inferInstance : MeasurableSpace X).prod 𝓕.predictable) inferInstance
    (fun p=>raw 𝓕 μ H Y R G c p.1 p.2) := by
  have hrow : @Measurable (X×(ℝ≥0×Ω)) C
      ((inferInstance : MeasurableSpace X).prod 𝓕.predictable) inferInstance
      (fun p=>gradientRow 𝓕 μ H Y R (G p.1) p.2) := by
    apply Finset.measurable_sum
    intro i _
    have hgrad := (hc.clm_apply (continuous_const (y:=EuclideanSpace.basisFun (Fin n) ℝ i))).measurable
    have hm := hgrad.comp (measurable_fst.prodMk
      (((PredictableClock.real_time_measurable 𝓕).comp measurable_snd).prodMk (hY.measurable.comp measurable_snd)))
    exact hm.smul ((Lp.stronglyMeasurable (R i)).measurable.comp measurable_snd)
  exact hrow.ite ((measurableSet_lt (PredictableClock.time_measurable 𝓕) measurable_const).preimage measurable_snd)
    measurable_const

include hc in
theorem continuous_parameter (p : ℝ≥0×Ω) :
    Continuous (fun x=>raw 𝓕 μ H Y R G c x p) := by
  by_cases ht : p.1<c
  · simp only [raw,ite_eq_left ht,gradientRow]
    apply continuous_finsetSum
    intro i _
    have hgrad := hc.comp (continuous_id.prodMk (continuous_const (y:=((p.1:ℝ),Y p))))
    exact (hgrad.clm_apply continuous_const).smul continuous_const
  · simp only [raw,ite_eq_right ht]
    exact continuous_const

variable (L : ℝ) (hL0 : 0≤L) (hL : ∀ x t z,‖fderiv ℝ (G x t) z‖≤L)
include hL0 hL in
theorem bound : ∀ᵐ p ∂(energyMeasure μ H).trim (predictable_le_product 𝓕),∀ x,
    ‖raw 𝓕 μ H Y R G c x p‖≤‖FiniteItoGradientMajorant.process 𝓕 μ H R L p‖ := by
  filter_upwards [FiniteItoGradientMajorant.family_bound 𝓕 μ H R L Y G hL0 hL] with p hp x
  by_cases ht : p.1<c
  · simpa only [raw,ite_eq_left ht] using hp x
  · simp only [raw,ite_eq_right ht,norm_zero]
    exact norm_nonneg _

end SHE.FiniteItoGradientFamily
