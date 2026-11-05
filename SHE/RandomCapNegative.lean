module

public import SHE.RandomNegativeRows
public import SHE.IncreasingCap

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 2500000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHE.RandomRowEnergy
open Set Filter MeasureTheory ProbabilityTheory AddCircle Real CircleHeat HeatMarkov NegativeNash
open scoped ENNReal
local instance randomCapNegative_periodPositive : Fact (0<(1:ℝ)) := ⟨zero_lt_one⟩
local instance randomCapNegative_exponentFinite : Fact ((2:ENNReal)≠⊤) := ⟨by simp⟩
local instance randomCapNegative_unitMeasurable : MeasurableSpace CircleL2 := borel _
local instance randomCapNegative_unitBorel : BorelSpace CircleL2 := ⟨rfl⟩
variable {Ω : Type*} [MeasurableSpace Ω]

theorem section_memLp_cap {F : Ω×UnitAddCircle→ℂ} (hF : Measurable F) (cap : Ω→ℝ)
    (hb : ∀ ω x,‖F (ω,x)‖≤cap ω) (ω : Ω) : MemLp (fun x=>F (ω,x)) 2 haarAddCircle :=
  MemLp.of_bound (hF.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable (cap ω)
    (ae_of_all _ (hb ω))

theorem row_ae_cap {F : Ω×UnitAddCircle→ℂ} (hF : Measurable F) (cap : Ω→ℝ)
    (hb : ∀ ω x,‖F (ω,x)‖≤cap ω) (ω : Ω) :
    (row F ω : UnitAddCircle→ℂ)=ᵐ[haarAddCircle] fun x=>F (ω,x) :=
  MeasurableL2Field.realizeL2_ae F (section_memLp_cap hF cap hb) ω

theorem row_measurable_cap {F : Ω×UnitAddCircle→ℂ} (hF : Measurable F) (cap : Ω→ℝ)
    (hb : ∀ ω x,‖F (ω,x)‖≤cap ω) : Measurable (row F) :=
  MeasurableL2Field.realizeL2_measurable hF (section_memLp_cap hF cap hb)

/-- The actual RMS negative-output estimate remains valid under a
sample-dependent coarse cap with a genuine second moment. The cap is
only used for applicability; the sharp constant retains the original
RMS Gaussian envelope and arbitrary input/score dependence. -/
theorem expected_dominated_negative_cap (μ : Measure Ω) [IsProbabilityMeasure μ]
    {F : Ω×UnitAddCircle→ℂ} (hF : Measurable F) (cap : Ω→ℝ)
    (hcap : Measurable cap) (hcap2 : Integrable (fun ω=>cap ω^2) μ)
    (hb : ∀ ω x,‖F (ω,x)‖≤cap ω)
    {Λ ρ t K : ℝ} (hΛ : 1≤Λ) (hρ : 0<ρ) (hρhalf : ρ<1/2)
    (ht : 0<t) (ht1 : t≤1) (hK : 0≤K) (a : UnitAddCircle)
    (hsharp : ∀ x,rms μ F x≤K*‖kernel (8*t) (by positivity) (x-a)‖) :
    Integrable (fun ω=>energy Λ ρ (row F ω)) μ ∧
      (∫ ω,energy Λ ρ (row F ω) ∂μ)≤GaussianNegativePacket.constant ρ*t^(ρ-1/2)*K^2 ∧
      (∫ ω,energy Λ ρ (row F ω) ∂μ)≤GaussianNegativePacket.traceConstant*Λ^(-ρ)*t^(-(1/2:ℝ))*K^2 := by
  let G : ℕ→Ω×UnitAddCircle→ℂ := fun n z=>if cap z.1≤(n:ℝ) then F z else 0
  have hG (n : ℕ) : Measurable (G n) :=
    hF.ite ((measurableSet_le hcap measurable_const).preimage measurable_fst) measurable_const
  have hGb (n : ℕ) (ω : Ω) (x : UnitAddCircle) : ‖G n (ω,x)‖≤(n:ℝ) := by
    dsimp only [G]
    split_ifs with h
    · exact (hb ω x).trans h
    · simp only [norm_zero,Nat.cast_nonneg]
  have hrows (n : ℕ) (ω : Ω) : row (G n) ω=if cap ω≤(n:ℝ) then row F ω else 0 := by
    apply Lp.ext
    filter_upwards [row_ae (hG n) (hGb n) ω,row_ae_cap hF cap hb ω,
      Lp.coeFn_zero ℂ 2 haarAddCircle] with x hx hy hz
    by_cases hc : cap ω≤(n:ℝ)
    · simp only [G, if_pos hc] at hx
      simpa only [if_pos hc] using hx.trans hy.symm
    · simp only [G, if_neg hc] at hx
      simpa only [if_neg hc] using hx.trans hz.symm
  have hGi (n : ℕ) (x : UnitAddCircle) : Integrable (fun ω=>‖G n (ω,x)‖^2) μ := by
    apply (integrable_const ((n:ℝ)^2)).mono'
      (((hG n).comp (measurable_id.prodMk measurable_const)).norm.pow_const 2).aestronglyMeasurable
    exact ae_of_all _ (fun ω => by
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      exact pow_le_pow_left₀ (norm_nonneg _) (hGb n ω x) 2)
  have hFi (x : UnitAddCircle) : Integrable (fun ω=>‖F (ω,x)‖^2) μ := by
    apply hcap2.mono' ((hF.comp (measurable_id.prodMk measurable_const)).norm.pow_const 2).aestronglyMeasurable
    exact ae_of_all _ (fun ω=>by
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      exact pow_le_pow_left₀ (norm_nonneg _) (hb ω x) 2)
  have hGsharp (n : ℕ) (x : UnitAddCircle) : rms μ (G n) x≤K*‖kernel (8*t) (by positivity) (x-a)‖ := by
    apply le_trans ?_ (hsharp x)
    apply Real.sqrt_le_sqrt
    apply integral_mono (hGi n x) (hFi x)
    intro ω
    dsimp only [G]
    split_ifs <;> simp only [le_rfl,norm_zero,zero_pow (by norm_num : (2:ℕ)≠0),sq_nonneg]
  have hcut (n : ℕ) := expected_dominated_negative μ (hG n) (Nat.cast_nonneg n) (hGb n)
    hΛ hρ hρhalf ht ht1 hK a (hGsharp n)
  let E : Ω→ℝ := fun ω=>energy Λ ρ (row F ω)
  have hE0 (ω : Ω) : 0≤E ω := tsum_nonneg (fun i=>
    mul_nonneg (Real.rpow_nonneg (by positivity) _) (sq_nonneg _))
  have hEc : Continuous (energy Λ ρ : CircleL2→ℝ) := by
    have he : (energy Λ ρ : CircleL2→ℝ)=StepInput.negativeEnergy 1 Λ ρ :=
      funext (energy_eq_negativeEnergy Λ ρ (zero_lt_one.trans_le hΛ))
    rw [he]
    exact FiniteHaar.continuous_negativeEnergy (zero_lt_one.trans_le hΛ) hρ.le
  have hEm : Measurable E := hEc.measurable.comp (row_measurable_cap hF cap hb)
  have hEn (n : ℕ) (ω : Ω) : energy Λ ρ (row (G n) ω)=if cap ω≤(n:ℝ) then E ω else 0 := by
    rw [hrows]
    split_ifs
    · rfl
    · have hz := FiniteHaar.negativeEnergy_le_L2 (κ:=1)
        (zero_lt_one.trans_le hΛ) hρ.le (0 : CircleL2)
      have hn : 0 ≤ energy Λ ρ (0 : CircleL2) := tsum_nonneg (fun i =>
        mul_nonneg (Real.rpow_nonneg (by positivity) _) (sq_nonneg _))
      rw [← energy_eq_negativeEnergy Λ ρ (zero_lt_one.trans_le hΛ)] at hz
      simp only [norm_zero, zero_pow (by norm_num : (2:ℕ)≠0), mul_zero] at hz
      exact le_antisymm hz hn
  have hci (n : ℕ) : Integrable (fun ω=>if cap ω≤(n:ℝ) then E ω else 0) μ :=
    (hcut n).1.congr (ae_of_all _ (hEn n))
  have hGρ := (HeatTrace.fractionalGaussianIntegral_pos hρhalf).le
  have hP0 : 0≤GaussianNegativePacket.constant ρ*t^(ρ-1/2)*K^2 := by
    unfold GaussianNegativePacket.constant
    have := GaussianNegativePacket.traceConstant_pos
    positivity
  have hQ0 : 0≤GaussianNegativePacket.traceConstant*Λ^(-ρ)*t^(-(1/2:ℝ))*K^2 := by
    have := GaussianNegativePacket.traceConstant_pos
    positivity
  have hp := IncreasingCap.integral_bound μ E cap hEm hcap hE0 hP0 hci (fun n =>
    (integral_congr_ae (ae_of_all _ (hEn n))).symm.trans_le (hcut n).2.1)
  have hq := IncreasingCap.integral_bound μ E cap hEm hcap hE0 hQ0 hci (fun n =>
    (integral_congr_ae (ae_of_all _ (hEn n))).symm.trans_le (hcut n).2.2)
  exact ⟨hp.1,hp.2,hq.2⟩

end SHE.RandomRowEnergy
