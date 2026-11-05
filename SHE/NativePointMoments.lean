module

public import SHE.NativePointBracket
public import SHE.StandardTerminalBDGPower

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

namespace SHE.NativePointMoments
open MeasureTheory StoppedFourier FiniteHaar PredictableL2
open scoped NNReal ENNReal
local instance nativePointMoments_periodPositive : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
local instance nativePointMoments_finiteExponent : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨by simp⟩
local instance nativePointMoments_rowSigma : MeasurableSpace RealHaarInput := borel RealHaarInput
local instance nativePointMoments_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩

variable {Ω : Type*} [MeasurableSpace Ω]

def pointInput (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›)
    (μ : Measure Ω) [IsProbabilityMeasure μ] (h : ℝ≥0)
    {ell M : ℝ} (hell : 0 < ell) (hM : 0 ≤ M)
    (f : ℝ≥0 × Ω → EllipticField ell M) (hf : StronglyMeasurable[𝓕.predictable] f)
    (x : HeatCircle) : Process (E := RealHaarInput) 𝓕 μ h :=
  NativeObservationEndpoint.process 𝓕 μ h hell hM f hf (T := (h : ℝ)) le_rfl x

def value (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›)
    (μ : Measure Ω) [IsProbabilityMeasure μ] (h : ℝ≥0)
    {ell M : ℝ} (hell : 0 < ell) (hM : 0 ≤ M)
    (f : ℝ≥0 × Ω → EllipticField ell M) (hf : StronglyMeasurable[𝓕.predictable] f)
    (I : StandardTerminalIto (C := RealHaarInput) (E := ℝ) 𝓕 μ h)
    (x : HeatCircle) : Lp ℝ 2 μ := I.integral (pointInput 𝓕 μ h hell hM f hf x)

/-- Actual native physical point observations have all fixed even
moments with the sharp quarter-time scaling. Only universal BDG at the
chosen moment is accepted input; the heat and bracket bounds are proved. -/
theorem endpoint_moment (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›)
    (μ : Measure Ω) [IsProbabilityMeasure μ] {h : ℝ≥0} (hh : (h : ℝ) ≤ 1)
    {ell M : ℝ} (hell : 0 < ell) (hM : 0 ≤ M)
    (f : ℝ≥0 × Ω → EllipticField ell M) (hf : StronglyMeasurable[𝓕.predictable] f)
    (I : StandardTerminalIto (C := RealHaarInput) (E := ℝ) 𝓕 μ h)
    (p : ℕ) (B : ℝ≥0)
    (hBDG : StandardTerminalBDGPower (C := RealHaarInput) (E := ℝ) p I B) (x : HeatCircle) :
    (∫⁻ ω, ENNReal.ofReal (‖value 𝓕 μ h hell hM f hf I x ω‖ ^ (2 * p)) ∂μ) ≤
      ENNReal.ofReal ((B : ℝ) * (ProfileVariance.upperConstant * M) ^ p *
        (h : ℝ) ^ ((p : ℝ) / 2)) := by
  have hK : 0 ≤ ProfileVariance.upperConstant * M * (h : ℝ) ^ (1 / 2 : ℝ) :=
    mul_nonneg (mul_nonneg ProfileVariance.upperConstant_pos.le hM) (Real.rpow_nonneg h.2 _)
  have hb := StandardTerminalBDGPower.moment_of_bracket_bound I hBDG
    (pointInput 𝓕 μ h hell hM f hf x) hK
    (NativePointBracket.bracket_bound 𝓕 μ hh hell hM f hf x)
  apply hb.trans_eq
  congr 1
  rw [mul_pow, ← Real.rpow_mul_natCast (x := (h : ℝ)) h.2 (1 / 2 : ℝ) p]
  rw [show (1 / 2 : ℝ) * p = (p : ℝ) / 2 by ring]
  ring

/-- A finite even moment bound supplies the actual L^(2p) membership,
so subsequent Hölder estimates need no extra integrability premise. -/
theorem memLp_of_even_moment {Y : Ω → ℝ} {μ : Measure Ω}
    (hY : AEStronglyMeasurable Y μ) {p : ℕ} (hp : 0 < p) {K : ℝ}
    (hb : (∫⁻ ω, ENNReal.ofReal (‖Y ω‖ ^ (2 * p)) ∂μ) ≤ ENNReal.ofReal K) :
    MemLp Y (2 * p : ℕ) μ := by
  have hfin : HasFiniteIntegral (fun ω => ‖Y ω‖ ^ (2 * p)) μ :=
    (hasFiniteIntegral_iff_ofReal (ae_of_all _ (fun _ => pow_nonneg (norm_nonneg _) _))).mpr
      (hb.trans_lt ENNReal.ofReal_lt_top)
  have hi : Integrable (fun ω => ‖Y ω‖ ^ (2 * p)) μ := ⟨hY.norm.pow _, hfin⟩
  have hp0 : (2 * p : ℕ) ≠ 0 := by omega
  apply (integrable_norm_rpow_iff (p := ((2 * p : ℕ) : ℝ≥0∞)) hY
    (by exact_mod_cast hp0) (by exact ENNReal.natCast_ne_top _)).mp
  simpa only [ENNReal.toReal_natCast, Real.rpow_natCast] using hi

theorem endpoint_memLp (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›)
    (μ : Measure Ω) [IsProbabilityMeasure μ] {h : ℝ≥0} (hh : (h : ℝ) ≤ 1)
    {ell M : ℝ} (hell : 0 < ell) (hM : 0 ≤ M)
    (f : ℝ≥0 × Ω → EllipticField ell M) (hf : StronglyMeasurable[𝓕.predictable] f)
    (I : StandardTerminalIto (C := RealHaarInput) (E := ℝ) 𝓕 μ h)
    {p : ℕ} (hp : 0 < p) (B : ℝ≥0)
    (hBDG : StandardTerminalBDGPower (C := RealHaarInput) (E := ℝ) p I B) (x : HeatCircle) :
    MemLp (value 𝓕 μ h hell hM f hf I x)
      (2 * p : ℕ) μ :=
  memLp_of_even_moment (Lp.aestronglyMeasurable _) hp (endpoint_moment 𝓕 μ hh hell hM f hf I p B hBDG x)

end SHE.NativePointMoments
