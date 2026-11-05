module

public import SHEStochastic.ScalarStoppedHeatClock
public import SHEStochastic.NativeRandomStopLocality
public import SHEStochastic.FiniteCylindricalParameterVersions
public import SHEStochastic.FiniteCylindricalLocality
public import SHEStochastic.FourierHeatInput

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section

namespace SHEStochastic.ScalarStoppedFourierLocality
open MeasureTheory Set SHE SHE.PredictableL2 SHE.DyadicApproximation AddCircle
open scoped NNReal ENNReal

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
  (W : ℝ≥0 → Ω → RealL2) (hW : StronglyMeasurable[F.predictable] (Function.uncurry W))
  (hc : ∀ ω,Continuous (fun t => W t ω))
  {g : ℝ → ℝ} {C β : ℝ≥0} (hg : HolderWith C β g) (hβ : 0<β) (hβ₁ : β≤1)
  (N : ℕ) (ψ : ℂ →L[ℝ] ℝ) (n : ℤ)

local notation "τ" => ContinuousNormExit.exit W N
local notation "v" t:max => ScalarStoppedHeatFourierInput.input F μ H W hW hc hg hβ hβ₁ N t ψ n
local notation "stop" => StoppedItoInputs.stop F μ H

omit [MeasurableSpace Ω] in
theorem exit_eq : UnboundedNativeHeatEquation.exit W N = τ := by
  unfold UnboundedNativeHeatEquation.exit ContinuousNormExit.exit
  simp only [UnboundedNativeHeatEquation.physical,LinearIsometry.norm_map]

/-- Locality compares the two representations on the original Brownian
space before the actual state exit. The deterministic Fourier multiplier
recovers the true heat age. -/
theorem compare {ι : Type*} [Countable ι] [DecidableEq ι]
    (P : FiniteScalarIto.Family F μ H ι) (e : HilbertBasis ι ℝ Noise)
    (hn : NullCompleteFiltration.ContainsNullSets F μ)
    (u : Process (E := Noise) F μ H)
    (hu : ∀ᵐ p ∂energyMeasure μ H,(p.1 : WithTop ℝ≥0)<τ p.2 →
      u p=FourierHeatInput.multiplier H n p •
        StateNoiseCovariance.row ν hβ hβ₁ hg (NativeFourierHeatCoordinate.weight ψ n)
          (UnboundedNativeHeatEquation.physical W p))
    (t : ℝ≥0) (ht : t≤H) :
    ∀ᵐ ω ∂μ,(t : WithTop ℝ≥0)<τ ω →
      (FiniteCylindricalIto.terminalIto P.toCoordinates e).integral (v t) ω =
        Real.exp (-(t : ℝ)*(n : ℝ)^2)*
          (FiniteCylindricalIto.terminalIto P.toCoordinates e).integral (stop t u) ω := by
  let k := Real.exp (-(t : ℝ)*(n : ℝ)^2)
  let w := k • stop t u
  let J := FiniteCylindricalIto.terminalIto P.toCoordinates e
  have hw : stop t w=w := by
    rw [show w=k • stop t u from rfl,StoppedInputAlgebra.stop_smul,StoppedInputAlgebra.stop_stop,min_self]
  have hτ : IsStoppingTime F τ := by
    rw [←exit_eq W N]
    exact UnboundedNativeHeatEquation.exit_stopping F W hW hc N
  have he := NativeRandomStopLocality.integral_eq_before F μ H J (FiniteCylindricalIto.pastLocality P e)
    (FiniteCylindricalIto.continuousStoppedVersions P e) hn (v t) w t
    (ScalarStoppedHeatClock.stop_input F μ H W hW hc hg hβ hβ₁ N ψ n t ht) hw τ hτ
  have hr : ∀ᵐ p ∂energyMeasure μ H,(p.1 : WithTop ℝ≥0)<τ p.2 → (v t) p=w p := by
    filter_upwards [ScalarStoppedHeatFourierInput.input_ae F μ H W hW hc hg hβ hβ₁ N t ψ n,
      StoppedItoInputs.stop_ae F μ H t u,ae_eq_of_ae_eq_trim (Lp.coeFn_smul k (stop t u)),hu]
      with p hv hst hsm hu hbefore
    change (v t) p=(k • stop t u) p
    rw [hv,hsm,Pi.smul_apply,hst]
    by_cases hp : p∈StoppedItoInputs.before (Ω := Ω) t
    · have hp' : p∈ScalarStoppedHeatFourierInput.before W N t := ⟨hp,hbefore⟩
      have hpt : (p.1 : ℝ)<t := hp
      rw [ScalarStoppedHeatFourierInput.row,indicator_of_mem hp',indicator_of_mem hp,hu hbefore,smul_smul]
      dsimp only [k,FourierHeatInput.multiplier]
      rw [min_eq_left (hpt.le.trans (by exact_mod_cast ht)),←Real.exp_add]
      congr 2
      ring
    · rw [ScalarStoppedHeatFourierInput.row,indicator_of_notMem
        (show p∉ScalarStoppedHeatFourierInput.before W N t from fun h => hp h.1),
        indicator_of_notMem hp,smul_zero]
  have hmap : J.integral w=k • J.integral (stop t u) := map_smul J.integral k _
  rw [hmap] at he
  filter_upwards [he hr,Lp.coeFn_smul k (J.integral (stop t u))] with ω he hsm hω
  have hh := he hω.le
  change J.integral (v t) ω = (k • J.integral (stop t u)) ω at hh
  simpa only [hsm,Pi.smul_apply,smul_eq_mul,k] using hh

end SHEStochastic.ScalarStoppedFourierLocality
