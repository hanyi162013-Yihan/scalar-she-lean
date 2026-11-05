module

public import SHE.FiniteItoGradientFamily
public import SHE.FiniteItoParameterResidual

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
namespace SHE.FiniteItoBorelGradient
open Set MeasureTheory PredictableL2 FiniteItoNoise PastItoInputs StoppedItoInputs Filter Topology
open scoped NNReal ENNReal
variable {Ω X C : Type*} [MeasurableSpace Ω]
variable [PseudoMetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [NormedAddCommGroup C] [InnerProductSpace ℝ C]
variable [MeasurableSpace C] [BorelSpace C] [SecondCountableTopology C]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [SFinite μ] (H : ℝ≥0)
variable {n : ℕ} (Y : ℝ≥0×Ω→WordRecursion.State n)
variable (hY : StronglyMeasurable[𝓕.predictable] Y) (R : Fin n→Process (E:=C) 𝓕 μ H)
variable (G : X→ℝ→WordRecursion.State n→ℝ)
variable (hgm : Measurable (fun p : X×(ℝ×WordRecursion.State n)=>fderiv ℝ (G p.1 p.2.1) p.2.2))
variable (L : ℝ) (hL0 : 0≤L) (hL : ∀ x t z,‖fderiv ℝ (G x t) z‖≤L)
variable (v c : ℝ≥0) (e : X)

local notation "g" => FiniteItoGradientFamily.raw 𝓕 μ H Y R G c
include hY hgm in
theorem measurable_raw : @Measurable (X×(ℝ≥0×Ω)) C
    ((inferInstance : MeasurableSpace X).prod 𝓕.predictable) inferInstance
    (fun p=>FiniteItoGradientFamily.raw 𝓕 μ H Y R G c p.1 p.2) := by
  have hrow : @Measurable (X×(ℝ≥0×Ω)) C
      ((inferInstance : MeasurableSpace X).prod 𝓕.predictable) inferInstance
      (fun p=>gradientRow 𝓕 μ H Y R (G p.1) p.2) := by
    apply Finset.measurable_sum
    intro i _
    have hgrad := (isBoundedBilinearMap_apply (𝕜:=ℝ)).continuous.measurable.comp (hgm.prodMk (measurable_const (a:=EuclideanSpace.basisFun (Fin n) ℝ i)))
    have hm := hgrad.comp (measurable_fst.prodMk
      (((PredictableClock.real_time_measurable 𝓕).comp measurable_snd).prodMk (hY.measurable.comp measurable_snd)))
    exact hm.smul ((Lp.stronglyMeasurable (R i)).measurable.comp measurable_snd)
  exact hrow.ite ((measurableSet_lt (PredictableClock.time_measurable 𝓕) measurable_const).preimage measurable_snd)
    measurable_const

local notation "hg" => measurable_raw 𝓕 μ H Y hY R G hgm c
local notation "major" => FiniteItoGradientMajorant.process 𝓕 μ H R L
local notation "hb" => FiniteItoGradientFamily.bound 𝓕 μ H Y R G c L hL0 hL

def input {u : Ω→X} (hu : Measurable[𝓕 v] u) : Process (E:=C) 𝓕 μ H :=
  PastParameterItoInput.input 𝓕 μ H v g hg major hb e hu

theorem input_ae {u : Ω→X} (hu : Measurable[𝓕 v] u) :
    input 𝓕 μ H Y hY R G hgm L hL0 hL v c e hu =ᵐ[energyMeasure μ H]
      fun p=>if v<p.1 ∧ p.1<c then gradientRow 𝓕 μ H Y R (G (u p.2)) p else 0 := by
  filter_upwards [PastParameterItoInput.input_ae 𝓕 μ H v g hg major hb e hu] with p hp
  change PastParameterItoInput.input 𝓕 μ H v g hg major hb e hu p=_
  rw [hp]
  by_cases h₁ : v<p.1 <;> by_cases h₂ : p.1<c <;>
    simp [PastParameterItoInput.raw,FiniteItoGradientFamily.raw,h₁,h₂]

/-- The random-gradient construction specializes exactly to the
ordinary deterministic-test gradient integral, with its ORIGINAL rows. -/
theorem constant_input_eq (x : X) (hG : AdmissibleGradient (G x)) :
    input 𝓕 μ H Y hY R G hgm L hL0 hL v c e (measurable_const (a:=x))=
      post 𝓕 μ H v (stop 𝓕 μ H c (gradientProcess 𝓕 μ H Y hY R (G x) hG)) := by
  apply PastItoAlgebra.eq_of_ambient_ae
  filter_upwards [input_ae 𝓕 μ H Y hY R G hgm L hL0 hL v c e (measurable_const (a:=x)),
    post_ae 𝓕 μ H v (stop 𝓕 μ H c (gradientProcess 𝓕 μ H Y hY R (G x) hG)),
    stop_ae 𝓕 μ H c (gradientProcess 𝓕 μ H Y hY R (G x) hG),
    gradientProcess_ae 𝓕 μ H Y hY R (G x) hG] with p hi hp hs hgradrow
  rw [hi,hp,hs]
  by_cases h₁ : v<p.1 <;> by_cases h₂ : p.1<c <;>
    simp [h₁,h₂,before,Set.indicator,hgradrow]

/-- Only continuity in the past parameter is needed for predictable-L²
selection; joint time/parameter continuity is not imposed. -/
theorem continuous_parameter
    (hc : ∀ t z,Continuous (fun x=>fderiv ℝ (G x t) z)) (p : ℝ≥0×Ω) :
    Continuous (fun x=>g x p) := by
  by_cases ht : p.1<c
  · simp only [FiniteItoGradientFamily.raw,ite_eq_left ht,gradientRow]
    apply continuous_finsetSum
    intro i _
    exact ((hc (p.1:ℝ) (Y p)).clm_apply continuous_const).smul continuous_const
  · simp only [FiniteItoGradientFamily.raw,ite_eq_right ht]
    exact continuous_const

end SHE.FiniteItoBorelGradient

