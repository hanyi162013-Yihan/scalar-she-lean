module
public import SHE.OrdinaryNamedLevelNoise
public import SHE.OrdinaryPhysicalRows

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
namespace SHE.OrdinaryLevelPhysicalInput
open Set MeasureTheory PredictableL2 FiniteHaar DyadicApproximation StoppedFourier
  NativeHeatObservation NativeObservationNaturality WordRecursion OrthogonalItoChannels
  CutoffWordLevel GaussianItoTest
open scoped NNReal ENNReal
local instance ordinaryLevelPhysicalInput_period:Fact (0<2*Real.pi):=⟨by positivity⟩
local instance ordinaryLevelPhysicalInput_realSigma:MeasurableSpace RealL2:=borel _
local instance ordinaryLevelPhysicalInput_realBorel:BorelSpace RealL2:=⟨rfl⟩
local instance ordinaryLevelPhysicalInput_nativeSigma:MeasurableSpace CircleL2:=borel _
local instance ordinaryLevelPhysicalInput_nativeBorel:BorelSpace CircleL2:=⟨rfl⟩
local instance ordinaryLevelPhysicalInput_rowSigma:MeasurableSpace RealHaarInput:=borel _
local instance ordinaryLevelPhysicalInput_rowBorel:BorelSpace RealHaarInput:=⟨rfl⟩
local instance ordinaryLevelPhysicalInput_blockSigma:MeasurableSpace (Both RealHaarInput):=borel _
local instance ordinaryLevelPhysicalInput_blockBorel:BorelSpace (Both RealHaarInput):=⟨rfl⟩
variable {Ω Y:Type}[MeasurableSpace Ω][MeasurableSpace Y]
variable {𝓕:Filtration ℝ≥0 ‹MeasurableSpace Ω›}{μ:Measure Ω}[IsProbabilityMeasure μ]
variable {H:ℝ≥0}{κ:ℝ}{a:ℝ→ℝ}{ell M:ℝ}(m:TwoChannelCutoffModel.Model 𝓕 μ H κ a ell M)
variable {R:ReferenceData}{n:ℕ}(L:Level R Y n)

theorem admissible_gradient(p:Y):FiniteItoNoise.AdmissibleGradient
    (backward (L.window p) (L.test p)):=by
  obtain ⟨C₀,_,hB₀⟩:=L.test_uniform.norm_bound
  obtain ⟨C,_,hB⟩:=L.test_uniform.fderiv.norm_bound
  refine ⟨BackwardRegularity.gaussian_gradient_joint_continuous _ (L.window p).continuous_path
    ((L.test_uniform.smooth p).of_le (by simp)) (hB₀ p) (hB p),C,?_⟩
  intro t z
  exact BackwardRegularity.gaussian_state_gradient_bound _
    ((L.test_uniform.smooth p).of_le (by simp)) (hB₀ p) (hB p) z

/-- The actual ordinary-U finite-Ito input is its literal native
gradient with the original two Haar channels, before any averaging. -/
theorem original_section_input (hh:R.horizon≤(H:ℝ)){η:ℝ}(hη:0<η)
    (hgap:∀p i,η≤(L.observations.observations p i).target-L.terminal p)(p:Y):
    ∃input:Process (E:=Both RealHaarInput) 𝓕 μ H,
      input=ᵐ[energyMeasure μ H] (fun z=>OrdinaryPhysicalGradient.raw m L (p,z)) ∧
      m.scalarIto.integral input=ᵐ[μ] OrdinaryUncutNoise.version m L p:=by
  let c:ℝ≥0:=(L.terminal p).toNNReal
  let v:ℝ≥0:=R.base.toNNReal
  have hc:(c:ℝ)=L.terminal p:=Real.coe_toNNReal _ (R.base_nonneg.trans (L.terminal_base p))
  have hv:(v:ℝ)=R.base:=Real.coe_toNNReal _ R.base_nonneg
  have hcH:c≤H:=by exact_mod_cast (show (c:ℝ)≤H by rw [hc];exact (L.terminal_horizon p).trans hh)
  have hvc:v≤c:=by exact_mod_cast (show (v:ℝ)≤(c:ℝ) by rw [hv,hc];exact L.terminal_base p)
  have hg:∀i,η≤(L.observations.observations p i).target-(c:ℝ):=by simpa only [hc] using hgap p
  let Y₀:=OrdinaryNamedIto.path m η (L.observations.observations p) c
  let hY:=OrdinaryNamedIto.path_predictable m (L.observations.observations p) c hη hg hcH
  let Rows:=OrdinaryNamedIto.rows m (L.observations.observations p) c hη hg
  let G:=backward (L.window p) (L.test p)
  have hG:=admissible_gradient L p
  let GP:=FiniteItoNoise.gradientProcess 𝓕 μ H Y₀ hY Rows G hG
  let input:=PastItoInputs.post 𝓕 μ H v (StoppedItoInputs.stop 𝓕 μ H (c:ℝ) GP)
  refine ⟨input,?_,?_⟩
  · filter_upwards [PastItoInputs.post_ae 𝓕 μ H v (StoppedItoInputs.stop 𝓕 μ H (c:ℝ) GP),
      StoppedItoInputs.stop_ae 𝓕 μ H (c:ℝ) GP,
      FiniteItoNoise.gradientProcess_ae 𝓕 μ H Y₀ hY Rows G hG,
      OrdinaryPhysicalRows.rows_ae m (L.observations.observations p) c hη hg] with z hp hstop hgrad hrows
    change input z=_
    rw [hp]
    by_cases hvz:v<z.1
    · rw [if_pos hvz,hstop]
      have hvzR:R.base<(z.1:ℝ):=by rw [←hv];exact_mod_cast hvz
      by_cases hzc:z.1<c
      · have hzcR:(z.1:ℝ)<L.terminal p:=by rw [←hc];exact_mod_cast hzc
        rw [Set.indicator_of_mem (show z∈StoppedItoInputs.before (Ω:=Ω) (c:ℝ) from by exact_mod_cast hzc),hgrad]
        have hYeq:Y₀ z=OrdinaryPhysicalGradient.mean m L (p,z):=by
          have he:=LocalNativeObservationIto.stoppedValue_eq_observe
            (Z:=L.observations.observations p) (b:=c) (hδ:=hη) (hgap:=hg) m.state
            (fun ω q=>m.physicalField (ω,q)) z.2 z.1.coe_nonneg (by exact_mod_cast hzc.le)
          have hm:=OrdinaryPhysicalGradient.mean_eq_observe m L p z hzcR
          simpa only [Y₀,OrdinaryNamedIto.path,Real.toNNReal_coe] using he.trans hm.symm
        simp only [OrdinaryPhysicalGradient.raw,if_pos (show R.base<(z.1:ℝ)∧(z.1:ℝ)<L.terminal p from ⟨hvzR,hzcR⟩),
          FiniteItoNoise.gradientRow,FiniteItoNoise.gradientCoefficient,hYeq]
        exact Finset.sum_congr rfl (fun i _=>by rw [hrows hzc i])
      · have hn:¬(z.1:ℝ)<L.terminal p:=by rw [←hc];exact_mod_cast hzc
        rw [Set.indicator_of_notMem (show z∉StoppedItoInputs.before (Ω:=Ω) (c:ℝ) from by exact_mod_cast hzc)]
        simp only [OrdinaryPhysicalGradient.raw,if_neg (show ¬(R.base<(z.1:ℝ)∧(z.1:ℝ)<L.terminal p) from fun hz=>hn hz.2)]
    · have hn:¬R.base<(z.1:ℝ):=by rw [←hv];exact_mod_cast hvz
      rw [if_neg hvz]
      simp only [OrdinaryPhysicalGradient.raw,if_neg (show ¬(R.base<(z.1:ℝ)∧(z.1:ℝ)<L.terminal p) from fun hz=>hn hz.1)]
  · have hn:=OrdinaryNamedLevelNoise.noise_eq_original m L hh hη hgap p
    have he:OrdinaryNamedIto.noise m (L.observations.observations p) c hη hg hcH v G=
        m.scalarIto.integral input:=congrArg (fun f:Lp ℝ 2 μ=>fun ω=>f ω)
      (FiniteItoPastNoise.noise_eq_post 𝓕 μ H Y₀ hY Rows m.scalarIto v c hvc G hG)
    change OrdinaryUncutNoise.version m L p=ᵐ[μ]
      OrdinaryNamedIto.noise m (L.observations.observations p) c hη hg hcH v G at hn
    rw [he] at hn
    exact hn.symm

end SHE.OrdinaryLevelPhysicalInput
