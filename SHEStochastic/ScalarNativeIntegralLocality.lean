module

public import SHEStochastic.NativeExponentialSubprobability

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1800000
noncomputable section

namespace SHEStochastic.ScalarNativeIntegralLocality
open MeasureTheory Filter
open scoped ENNReal NNReal Topology

variable {Ω C ι : Type*} [MeasurableSpace Ω] [Countable ι] [DecidableEq ι]
  [NormedAddCommGroup C] [InnerProductSpace ℝ C] [CompleteSpace C]
  [MeasurableSpace C] [BorelSpace C] [SecondCountableTopology C]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {H : ℝ≥0}
  (P : FiniteScalarIto.Family F μ H ι) (e : HilbertBasis ι ℝ C)

local notation "νin" => FiniteScalarIto.inputMeasure F μ H
local notation "I" => FiniteCylindricalIto.rawIntegral P.toCoordinates e

/-- The actual native terminal integral vanishes wherever its own
terminal energy vanishes. This uses the positive-exponential
subprobability theorem for each signed exponential test. -/
theorem zero_on_zero_energy (u : Lp C 2 νin) :
    ∀ᵐ ω ∂μ, NativeEnergy.energy u ω = 0 → I u ω = 0 := by
  have hOneSign (a : ℝ) :
      ∀ᵐ ω ∂μ, NativeEnergy.energy u ω = 0 → a*I u ω ≤ 0 := by
    let f (n : ℕ) (ω : Ω) := ENNReal.ofReal (NativeExponential.density P e ((n : ℝ)*a) u ω)
    have hm (n : ℕ) : Measurable (f n) :=
      (NativeExponential.stronglyMeasurable P e _ u).measurable.ennreal_ofReal
    have hb (n : ℕ) : (∫⁻ ω, f n ω ∂μ) ≤ 1 := by
      obtain ⟨hi,he⟩ := NativeExponentialSubprobability.integrable_and_le_one P e ((n : ℝ)*a) u
      unfold f
      rw [←ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ (fun ω => (Real.exp_pos _).le))]
      exact (ENNReal.ofReal_le_ofReal he).trans_eq ENNReal.ofReal_one
    have hL : (∫⁻ ω, liminf (fun n => f n ω) atTop ∂μ) ≤ 1 :=
      by
      refine (lintegral_liminf_le hm).trans ?_
      calc
        liminf (fun n => ∫⁻ ω, f n ω ∂μ) atTop ≤ liminf (fun _ : ℕ => (1 : ℝ≥0∞)) atTop :=
          liminf_le_liminf (Eventually.of_forall hb)
        _ = 1 := liminf_const _
    have hMeas : Measurable (fun ω => liminf (fun n => f n ω) atTop) := by
      apply Measurable.liminf
      exact hm
    filter_upwards [ae_lt_top hMeas (ne_top_of_le_ne_top (by simp) hL)] with ω hω h0
    by_contra! hp
    have hTo : Tendsto (fun n : ℕ => (n : ℝ)*(a*I u ω)) atTop atTop :=
      tendsto_natCast_atTop_atTop.atTop_mul_const hp
    have hExp : Tendsto (fun n : ℕ => ENNReal.ofReal (Real.exp ((n : ℝ)*(a*I u ω)))) atTop (𝓝 ⊤) :=
      ENNReal.tendsto_ofReal_atTop.comp (Real.tendsto_exp_atTop.comp hTo)
    have heq : (fun n : ℕ => f n ω)=fun n : ℕ => ENNReal.ofReal (Real.exp ((n : ℝ)*(a*I u ω))) := by
      funext n
      simp only [f,NativeExponential.density,h0,mul_zero,zero_div,sub_zero,mul_assoc]
    rw [heq,hExp.liminf_eq] at hω
    exact lt_irrefl _ hω
  filter_upwards [hOneSign 1,hOneSign (-1)] with ω hp hn h0
  have h₁ := hp h0
  have h₂ := hn h0
  linarith

/-- Equality of the native integrand on a path, almost everywhere in
physical time, gives equality of the native terminal integral there. -/
theorem congr_on_time_fibres (u v : Lp C 2 νin) :
    ∀ᵐ ω ∂μ, (∀ᵐ t ∂MathFin.ItoIntegralCLM.timeMeasure_T H,u (t,ω)=v (t,ω)) →
      I u ω=I v ω := by
  let w := u-v
  have hSub := NativeEnergy.energy_ae_of_ae w (fun p => u p-v p) (Lp.coeFn_sub u v)
  have hi := zero_on_zero_energy P e w
  have hdiff : I w = I u-I v := map_sub _ _ _
  filter_upwards [hSub,hi,Lp.coeFn_sub (I u) (I v)] with ω hS hI hD hEq
  have he : NativeEnergy.energy w ω=0 := by
    rw [hS]
    apply integral_eq_zero_of_ae
    filter_upwards [hEq] with t ht
    simp only [ht,sub_self,norm_zero,zero_pow (by norm_num : (2 : ℕ) ≠ 0),Pi.zero_apply]
  rw [hdiff,hD,Pi.sub_apply] at hI
  exact sub_eq_zero.mp (hI he)

end SHEStochastic.ScalarNativeIntegralLocality
