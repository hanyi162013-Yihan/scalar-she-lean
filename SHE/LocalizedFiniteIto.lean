module

public import SHE.LocalizedGradientLimits
public import SHE.LocalizedPathStability
public import SHE.StandardFiniteIto
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
noncomputable section

namespace SHE.LocalizedFiniteIto
open MeasureTheory Set Filter PredictableL2 FiniteItoNoise LocalizedItoTest
open scoped NNReal ENNReal Topology
local instance localizedFiniteIto_exponent : Fact ((1:ENNReal)≤2) := ⟨by norm_num⟩
variable {Ω C : Type*} [MeasurableSpace Ω]
variable [NormedAddCommGroup C] [InnerProductSpace ℝ C] [CompleteSpace C]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)

/-- The original bounded-test universal Itô formula implies its genuine
linear-time-growth smooth-test extension. Expanding actual state cutoffs,
predictable-L² gradient convergence and a subsequence argument discharge
the limit; no larger stochastic Itô package is assumed. -/
theorem formula (J : StandardTerminalIto (C := C) (E := ℝ) 𝓕 μ H)
    (hJ : StandardFiniteIto.Universal 𝓕 μ H J) {k : ℕ}
    (R : Fin k→Process (E := C) 𝓕 μ H) (z : WordRecursion.State k)
    (Y : ℝ≥0×Ω→WordRecursion.State k) (hY : StronglyMeasurable[𝓕.predictable] Y)
    (hc : ∀ ω,Continuous (fun t => Y (t,ω)))
    (hRep : ∀ t : ℝ≥0,t≤H → (fun ω => Y (t,ω))=ᵐ[μ] StandardFiniteIto.vectorIntegral 𝓕 μ H J z R t)
    {a b : ℝ} (ha : 0≤a) (hab : a≤b) (hb : b≤(H:ℝ))
    (G dG : ℝ→WordRecursion.State k→ℝ) (hG : SmoothTimeTest a b G dG) :
    ∀ᵐ ω ∂μ,G b (Y (b.toNNReal,ω))=G a (Y (a.toNNReal,ω))+
      noise 𝓕 μ H Y hY R J a b G ω+
      ∫ t in a..b,dG t (Y (t.toNNReal,ω))+(1/2:ℝ)*
        GaussianTaylorAverage.covarianceAction (StandardFiniteIto.rowCovariance 𝓕 μ H R ω t)
          (GaussianTaylor.hessian (G t) (Y (t.toNNReal,ω))) := by
  have hnoise := LocalizedGradientLimits.noise_tendsto 𝓕 μ H Y hY R J a b G hG.continuous hG.uniformSmooth
  obtain ⟨ns,hns,hAE⟩ := (tendstoInMeasure_of_tendsto_Lp hnoise).exists_seq_tendsto_ae
  have hform : ∀ᵐ ω ∂μ,∀ n,
      localized n G b (Y (b.toNNReal,ω))=localized n G a (Y (a.toNNReal,ω))+
        noise 𝓕 μ H Y hY R J a b (localized n G) ω+
        ∫ t in a..b,localized n dG t (Y (t.toNNReal,ω))+(1/2:ℝ)*
          GaussianTaylorAverage.covarianceAction (StandardFiniteIto.rowCovariance 𝓕 μ H R ω t)
            (GaussianTaylor.hessian (localized n G t) (Y (t.toNNReal,ω))) :=
    ae_all_iff.mpr (fun n => hJ.formula R z Y hY hc hRep ha hab hb
      (localized n G) (localized n dG) (regular_localized hG n))
  filter_upwards [hAE,hform] with ω hnoiseω hformω
  let I : ℝ := ∫ t in a..b,dG t (Y (t.toNNReal,ω))+(1/2:ℝ)*
    GaussianTaylorAverage.covarianceAction (StandardFiniteIto.rowCovariance 𝓕 μ H R ω t)
      (GaussianTaylor.hessian (G t) (Y (t.toNNReal,ω)))
  have hpath : Continuous (fun t : ℝ => Y (t.toNNReal,ω)) := (hc ω).comp continuous_real_toNNReal
  have hstable := LocalizedPathStability.eventually_jets_on_path a b G dG
    (fun t => Y (t.toNNReal,ω)) hpath.continuousOn
  have hconstant : ∀ᶠ n in atTop,
      noise 𝓕 μ H Y hY R J a b (localized (ns n) G) ω=
        G b (Y (b.toNNReal,ω))-G a (Y (a.toNNReal,ω))-I := by
    filter_upwards [hns.tendsto_atTop.eventually hstable] with n hn
    have hf := hformω (ns n)
    rw [(hn b ⟨hab,le_rfl⟩).1,(hn a ⟨le_rfl,hab⟩).1] at hf
    have hi : (∫ t in a..b,localized (ns n) dG t (Y (t.toNNReal,ω))+(1/2:ℝ)*
        GaussianTaylorAverage.covarianceAction (StandardFiniteIto.rowCovariance 𝓕 μ H R ω t)
          (GaussianTaylor.hessian (localized (ns n) G t) (Y (t.toNNReal,ω))))=I := by
      apply intervalIntegral.integral_congr
      intro t ht
      have ht' : t∈Icc a b := by simpa only [uIcc_of_le hab] using ht
      dsimp only
      rw [(hn t ht').2.2.1,(hn t ht').2.2.2]
    rw [hi] at hf
    linarith
  have hcst : Tendsto (fun n => noise 𝓕 μ H Y hY R J a b (localized (ns n) G) ω) atTop
      (𝓝 (G b (Y (b.toNNReal,ω))-G a (Y (a.toNNReal,ω))-I)) :=
    tendsto_const_nhds.congr' (hconstant.mono (fun _ hn => hn.symm))
  have he := tendsto_nhds_unique hnoiseω hcst
  change G b (Y (b.toNNReal,ω))=G a (Y (a.toNNReal,ω))+noise 𝓕 μ H Y hY R J a b G ω+I
  linarith

end SHE.LocalizedFiniteIto
