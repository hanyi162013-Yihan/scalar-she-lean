module

public import SHE.RandomCapNegative

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHE.RandomRowEnergy
open Set Filter MeasureTheory ProbabilityTheory AddCircle Real CircleHeat HeatMarkov NegativeNash
open scoped ENNReal
local instance randomCapAE_periodPositive : Fact (0 < (1:ℝ)) := ⟨zero_lt_one⟩
local instance randomCapAE_exponentFinite : Fact ((2:ENNReal) ≠ ⊤) := ⟨by simp⟩
local instance randomCapAE_measurableSpace : MeasurableSpace CircleL2 := borel _
local instance randomCapAE_borelSpace : BorelSpace CircleL2 := ⟨rfl⟩
variable {Ω : Type*} [MeasurableSpace Ω]

/-- The sharp spatial RMS statement is needed only on its genuine
almost-everywhere set. The original random L² row is retained exactly. -/
theorem expected_dominated_negative_cap_ae (μ : Measure Ω) [IsProbabilityMeasure μ]
    {F : Ω×UnitAddCircle→ℂ} (hF : Measurable F) (cap : Ω→ℝ)
    (hcap : Measurable cap) (hcap2 : Integrable (fun ω=>cap ω^2) μ)
    (hb : ∀ ω x,‖F (ω,x)‖≤cap ω)
    {Λ ρ t K : ℝ} (hΛ : 1≤Λ) (hρ : 0<ρ) (hρhalf : ρ<1/2)
    (ht : 0<t) (ht1 : t≤1) (hK : 0≤K) (a : UnitAddCircle)
    (hsharp : ∀ᵐ x ∂haarAddCircle,
      rms μ F x≤K*‖kernel (8*t) (by positivity) (x-a)‖) :
    Integrable (fun ω=>energy Λ ρ (row F ω)) μ ∧
      (∫ ω,energy Λ ρ (row F ω) ∂μ)≤GaussianNegativePacket.constant ρ*t^(ρ-1/2)*K^2 ∧
      (∫ ω,energy Λ ρ (row F ω) ∂μ)≤GaussianNegativePacket.traceConstant*Λ^(-ρ)*t^(-(1/2:ℝ))*K^2 := by
  classical
  let S : Set UnitAddCircle := {x | rms μ F x≤K*‖kernel (8*t) (by positivity) (x-a)‖}
  have hker : Continuous (fun x : UnitAddCircle => kernel (8*t) (by positivity) (x-a)) :=
    (kernel (8*t) (by positivity)).continuous.comp (continuous_id.sub continuous_const)
  have hS : MeasurableSet S := measurableSet_le (rms_measurable μ hF)
    (measurable_const.mul hker.measurable.norm)
  let G : Ω×UnitAddCircle→ℂ := fun p=>if p.2∈S then F p else 0
  have hG : Measurable G := hF.ite (hS.preimage measurable_snd) measurable_const
  have hcap0 (ω : Ω) : 0≤cap ω := (norm_nonneg (F (ω,0))).trans (hb ω 0)
  have hGb (ω : Ω) (x : UnitAddCircle) : ‖G (ω,x)‖≤cap ω := by
    dsimp only [G]
    split_ifs
    · exact hb ω x
    · simpa only [norm_zero] using hcap0 ω
  have hs (x : UnitAddCircle) : rms μ G x≤K*‖kernel (8*t) (by positivity) (x-a)‖ := by
    by_cases hx : x∈S
    · have hh : rms μ F x≤K*‖kernel (8*t) (by positivity) (x-a)‖ := hx
      simpa only [rms,G,ite_eq_left hx] using hh
    · simp only [rms,G,ite_eq_right hx,norm_zero,ProfileL2.normTwo,
        zero_pow (by norm_num : (2:ℕ)≠0),integral_zero,Real.sqrt_zero]
      exact mul_nonneg hK (norm_nonneg _)
  have he (ω : Ω) : row G ω=row F ω := by
    apply Lp.ext
    filter_upwards [row_ae_cap hG cap hGb ω,row_ae_cap hF cap hb ω,hsharp] with x hx hy hsx
    change row G ω x=G (ω,x) at hx
    change row F ω x=F (ω,x) at hy
    have hg : G (ω,x)=F (ω,x) := ite_eq_left hsx
    exact hx.trans (hg.trans hy.symm)
  have h := expected_dominated_negative_cap μ hG cap hcap hcap2 hGb hΛ hρ hρhalf ht ht1 hK a hs
  simpa only [he] using h

end SHE.RandomRowEnergy
