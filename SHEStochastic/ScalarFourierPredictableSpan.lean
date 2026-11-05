module

public import SHEStochastic.ScalarGrowingFourierInput
public import SHEStochastic.ScalarNoiseRowSeparation
public import SHEStochastic.NativeRowRepresentatives
public import Mathlib.MeasureTheory.Function.AEEqOfIntegral

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section

namespace SHEStochastic.ScalarFourierPredictableSpan
open MeasureTheory Set SHE SHE.PredictableL2 SHE.DyadicApproximation AddCircle
open scoped NNReal ENNReal InnerProductSpace

local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance : Fact (0 < 2*Real.pi) := ⟨by positivity⟩
local instance : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by simp⟩
local notation "ν" => haarAddCircle (T := 2*Real.pi)
local notation "Noise" => Lp ℝ 2 ν
local instance : MeasurableSpace Noise := borel _
local instance : BorelSpace Noise := ⟨rfl⟩
local instance : SecondCountableTopology Noise :=
  NativePhysicalState.equivalence.symm.toHomeomorph.secondCountableTopology

variable {Ω : Type*} [MeasurableSpace Ω]
  (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)

structure Cell where
  left : ℝ≥0
  right : ℝ≥0
  ordered : left≤right
  event : Set Ω
  past : MeasurableSet[F left] event

def Cell.region (c : Cell F) : Set (ℝ≥0×Ω) := Ioc c.left c.right ×ˢ c.event

theorem Cell.region_measurable (c : Cell F) : MeasurableSet[F.predictable] (c.region F) :=
  measurableSet_predictable_Ioc_prod c.left c.right c.past

local notation "νin" => FiniteScalarIto.inputMeasure F μ H

def cell (r : Lp Noise 2 νin) (c : Cell F) : Lp Noise 2 νin := by
  let _ : MeasurableSpace (ℝ≥0×Ω) := F.predictable
  exact ((Lp.memLp r).indicator (c.region_measurable F).nullMeasurableSet).toLp ((c.region F).indicator r)

omit [IsProbabilityMeasure μ] in
theorem cell_ae (r : Lp Noise 2 νin) (c : Cell F) :
    cell F μ H r c =ᵐ[νin] (c.region F).indicator r := by
  let _ : MeasurableSpace (ℝ≥0×Ω) := F.predictable
  exact ((Lp.memLp r).indicator (c.region_measurable F).nullMeasurableSet).coeFn_toLp

variable (W : ℝ≥0 → Ω → RealL2) (hW : StronglyMeasurable[F.predictable] (Function.uncurry W))
  {g : ℝ → ℝ} {C β : ℝ≥0} (hg : HolderWith C β g) (hβ : 0<β) (hβ₁ : β≤1)
  (hM : Integrable (fun p : ℝ≥0×Ω => ‖W p.1 p.2‖^2) (energyMeasure μ H))

def row (ψ : ℂ →L[ℝ] ℝ) (n : ℤ) : Lp Noise 2 νin :=
  FiniteCylindricalIto.processTransport (ScalarGrowingFourierInput.input F μ H W hW hg hβ hβ₁ ψ n hM)

theorem row_ae (ψ : ℂ →L[ℝ] ℝ) (n : ℤ) :
    row F μ H W hW hg hβ hβ₁ hM ψ n =ᵐ[νin] ScalarGrowingFourierInput.row H W hg hβ hβ₁ ψ n :=
  NativeRowRepresentatives.transport_ae _ _
    (ScalarGrowingFourierInput.predictable F H W hW hg hβ hβ₁ ψ n)
    (ScalarGrowingFourierInput.input_ae F μ H W hW hg hβ hβ₁ ψ n hM)

abbrev Index := (ℂ →L[ℝ] ℝ)×ℤ×Cell F

def generator (i : Index F) : Lp Noise 2 νin :=
  cell F μ H (row F μ H W hW hg hβ hβ₁ hM i.1 i.2.1) i.2.2

local notation "r" => row F μ H W hW hg hβ hβ₁ hM
local notation "V" => Submodule.span ℝ (range (generator F μ H W hW hg hβ hβ₁ hM))

private theorem inner_zero (v : Lp Noise 2 νin) (hv : v∈Vᗮ) (ψ : ℂ →L[ℝ] ℝ) (n : ℤ) :
    ∀ᵐ p ∂νin,inner ℝ (r ψ n p) (v p)=0 := by
  let _ : MeasurableSpace (ℝ≥0×Ω) := F.predictable
  let f (p : ℝ≥0×Ω) := inner ℝ (r ψ n p) (v p)
  have hI : Integrable f νin := by
    apply ((Lp.memLp (r ψ n)).norm.integrable_mul (Lp.memLp v).norm).mono'
      (((Lp.stronglyMeasurable (r ψ n)).inner (Lp.stronglyMeasurable v)).aestronglyMeasurable)
    exact ae_of_all _ fun p => abs_real_inner_le_norm _ _
  have hs (c : Cell F) : ∫ p in c.region F,f p ∂νin=0 := by
    have hc : cell F μ H (r ψ n) c∈V := Submodule.subset_span ⟨(ψ,n,c),rfl⟩
    have he := (Submodule.mem_orthogonal V v).mp hv _ hc
    rw [L2.inner_def] at he
    rw [←integral_indicator (c.region_measurable F)]
    refine (integral_congr_ae ?_).trans he
    filter_upwards [cell_ae F μ H (r ψ n) c] with p hp
    rw [hp]
    by_cases h : p∈c.region F <;> simp [h,f,inner_zero_left]
  have hR (S : Set (ℝ≥0×Ω))
      (hS : S ∈ FilteredItoCLM.predictableRect (𝓖 := F) (B := fun _ _ => (0 : ℝ)) (fun _ => measurable_const)) :
      ∫ p in S,f p ∂νin=0 := by
    rcases hS with ⟨A,hA,rfl⟩ | ⟨s,t,hst,A,hA,rfl⟩
    · apply setIntegral_measure_zero
      have hm := measurableSet_predictable_singleton_bot_prod (𝓕 := F) hA
      rw [NativeRowRepresentatives.inputMeasure_eq,trim_measurableSet_eq _ hm,energyMeasure,
        Measure.prod_prod]
      simp
    · exact hs ⟨s,t,hst.le,A,hA⟩
  have he := Integrable.ae_eq_zero_of_forall_setIntegral_eq_zero hI (fun s hs _ =>
    FilteredItoCLM.setIntegral_eq_zero_of_orthogonal_pred (𝓖 := F) (B := fun _ _ => (0 : ℝ))
      H (fun _ => measurable_const) hI hR s hs)
  exact he

/-- Predictable past rectangles multiplying the actual scalar diffusion
Fourier rows span a dense subspace of all predictable noise directions. -/
theorem dense_span (h₀ : ∀ x,g x≠0) : (V).topologicalClosure=⊤ := by
  have hOrth : Vᗮ=⊥ := by
    apply (Submodule.eq_bot_iff _).mpr
    intro v hv
    apply Lp.ext
    filter_upwards [ae_all_iff.mpr (fun n => inner_zero F μ H W hW hg hβ hβ₁ hM v hv Complex.reCLM n),
      ae_all_iff.mpr (fun n => inner_zero F μ H W hW hg hβ hβ₁ hM v hv Complex.imCLM n),
      ae_all_iff.mpr (fun n => row_ae F μ H W hW hg hβ hβ₁ hM Complex.reCLM n),
      ae_all_iff.mpr (fun n => row_ae F μ H W hW hg hβ hβ₁ hM Complex.imCLM n),
      Lp.coeFn_zero Noise 2 νin] with p hre him hr hi hz
    rw [hz,Pi.zero_apply]
    have hh (ψ : ℂ →L[ℝ] ℝ) (n : ℤ)
        (h : inner ℝ (r ψ n p) (v p)=0)
        (hrow : r ψ n p=ScalarGrowingFourierInput.row H W hg hβ hβ₁ ψ n p) :
        inner ℝ (StateNoiseCovariance.row ν hβ hβ₁ hg (NativeFourierHeatCoordinate.weight ψ n)
          (UnboundedNativeHeatEquation.physical W p)) (v p)=0 := by
      rw [hrow,ScalarGrowingFourierInput.row,real_inner_smul_left] at h
      exact (mul_eq_zero.mp h).resolve_left (Real.exp_ne_zero _)
    exact ScalarNoiseRowSeparation.eq_zero hg hβ hβ₁ h₀
      (UnboundedNativeHeatEquation.physical W p) (v p)
      (fun n => hh Complex.reCLM n (hre n) (hr n))
      (fun n => hh Complex.imCLM n (him n) (hi n))
  rw [←Submodule.orthogonal_orthogonal_eq_closure,hOrth,Submodule.bot_orthogonal_eq_top]

end SHEStochastic.ScalarFourierPredictableSpan
