module
public import SHE.CanonicalContinuousStateDriver
public import SHE.BoundedPastItoMultiplier
public import SHE.RotatedCylindricalCoordinates
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
namespace SHE.CanonicalScalarItoCells
open MeasureTheory PredictableL2 FiniteHaar CanonicalContinuousStateDriver
open scoped NNReal ENNReal Topology
local instance canonicalCells_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance canonicalCells_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
variable (H l r : ℝ≥0) (hl : l≤H) (hr : r≤H)
variable (Φ : E→RealHaarInput) (i : HaarNode)

def value (p : Space (E:=E) (ι:=HaarNode) H) : ℝ :=
  Φ (p.1 ⟨l, l.2, by exact_mod_cast hl⟩) i *
    (p.2 i ⟨r,r.2,by exact_mod_cast hr⟩-p.2 i ⟨l,l.2,by exact_mod_cast hl⟩)

theorem value_measurable (hΦ : Measurable Φ) :
    Measurable (value H l r hl hr Φ i) := by
  have hs : Measurable (fun p:Space (E:=E) (ι:=HaarNode) H=>
      Φ (p.1 ⟨l,l.2,by exact_mod_cast hl⟩) i) :=
    (lp.evalCLM ℝ (fun _:HaarNode=>ℝ) 2 i).continuous.measurable.comp
      (hΦ.comp ((ContinuousMap.measurable_eval _).comp measurable_fst))
  exact hs.mul (((ContinuousMap.measurable_eval _).comp
    ((measurable_pi_apply i).comp measurable_snd)).sub
      ((ContinuousMap.measurable_eval _).comp ((measurable_pi_apply i).comp measurable_snd)))

variable {Ω : Type*} [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ]
variable (J : StandardTerminalIto (C:=RealHaarInput) (E:=ℝ) 𝓕 μ H)

def coordinate (t : ℝ≥0) (ω : Ω) : ℝ :=
  J.integral (StoppedItoInputs.stop 𝓕 μ H (t:ℝ)
    (RotatedCylindricalCoordinates.constant 𝓕 μ H (lp.single 2 i (1:ℝ)))) ω

/-- Every canonical finite cell is the SAME actual original stochastic
integral of its literal bounded past-known row. No stochastic integral
is assumed to be a path functional in this statement. -/
theorem exists_input (hlr : l≤r) (hΦ : Measurable Φ) (M : ℝ) (hM : 0≤M)
    (hbound : ∀u,‖Φ u‖≤M) (hlocal : StandardTerminalPastLocality J)
    (U : ℝ≥0→Ω→E) (hUa : StronglyAdapted 𝓕 U) :
    ∃f:Process (E:=RealHaarInput) 𝓕 μ H,
      f=ᵐ[energyMeasure μ H] (fun p=>if l<p.1 ∧ p.1<r then
        (Φ (U l p.2) i) • lp.single 2 i (1:ℝ) else 0) ∧
      J.integral f=ᵐ[μ] (fun ω=>Φ (U l ω) i*
        (coordinate H i 𝓕 μ J r ω-coordinate H i 𝓕 μ J l ω)) := by
  have hα : StronglyMeasurable[𝓕 l] (fun ω=>Φ (U l ω) i) :=
    (lp.evalCLM ℝ (fun _:HaarNode=>ℝ) 2 i).continuous.comp_stronglyMeasurable
      ((hΦ.comp (hUa l).measurable).stronglyMeasurable)
  have hb : ∀ω,|Φ (U l ω) i|≤M := fun ω=>by
    simpa only [Real.norm_eq_abs] using
      (lp.norm_apply_le_norm (by norm_num : (2:ENNReal)≠0) (Φ (U l ω)) i).trans (hbound _)
  obtain ⟨f,hf,hJ⟩ := BoundedPastItoMultiplier.increment 𝓕 μ H l J hlocal r hlr
    (RotatedCylindricalCoordinates.constant 𝓕 μ H (lp.single 2 i (1:ℝ)))
    (fun ω=>Φ (U l ω) i) hα M hM hb
  refine ⟨f,?_,hJ⟩
  filter_upwards [hf,RotatedCylindricalCoordinates.constant_ae 𝓕 μ H
    (lp.single (E:=fun _:HaarNode=>ℝ) 2 i (1:ℝ))] with p hf hc
  rw [hf]
  split_ifs
  · rw [hc]
  · rfl

/-- For continuous versions of those SAME coordinates, the stochastic
cell equals the explicit measurable state-and-driver path functional. -/
theorem exists_canonical_input (hlr : l≤r) (hΦ : Measurable Φ) (M : ℝ) (hM : 0≤M)
    (hbound : ∀u,‖Φ u‖≤M) (hlocal : StandardTerminalPastLocality J)
    (U : ℝ≥0→Ω→E) (hc : ∀ω,Continuous (fun t=>U t ω)) (hUa : StronglyAdapted 𝓕 U)
    (W : HaarNode→ℝ≥0→Ω→ℝ) (hWc : ∀i ω,Continuous (fun t=>W i t ω))
    (hWl : W i l=ᵐ[μ] coordinate H i 𝓕 μ J l)
    (hWr : W i r=ᵐ[μ] coordinate H i 𝓕 μ J r) :
    ∃f:Process (E:=RealHaarInput) 𝓕 μ H,
      f=ᵐ[energyMeasure μ H] (fun p=>if l<p.1 ∧ p.1<r then
        (Φ (U l p.2) i) • lp.single 2 i (1:ℝ) else 0) ∧
      J.integral f=ᵐ[μ] (fun ω=>value H l r hl hr Φ i
        (bundle H U hc W hWc ω)) := by
  obtain ⟨f,hf,hi⟩ := exists_input H l r Φ i 𝓕 μ J hlr hΦ M hM hbound hlocal U hUa
  refine ⟨f,hf,?_⟩
  filter_upwards [hi,hWl,hWr] with ω hi hl' hr'
  simp only [value,bundle,NativeContinuousPath.path_apply,Real.toNNReal_coe]
  rw [hl',hr']
  exact hi
end SHE.CanonicalScalarItoCells
