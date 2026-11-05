module
public import SHE.OrdinaryNamedIto
public import SHE.OrdinaryUncutNoise

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
namespace SHE.OrdinaryNamedLevelNoise
open Set MeasureTheory PredictableL2 FiniteHaar DyadicApproximation StoppedFourier
  NativeHeatObservation NativeObservationNaturality WordRecursion OrthogonalItoChannels
  CutoffWordLevel IntegratedPhysicalStep GaussianItoTest
open scoped NNReal ENNReal
local instance ordinaryNamedLevelNoise_realSigma:MeasurableSpace RealL2:=borel _
local instance ordinaryNamedLevelNoise_realBorel:BorelSpace RealL2:=⟨rfl⟩
local instance ordinaryNamedLevelNoise_nativeSigma:MeasurableSpace CircleL2:=borel _
local instance ordinaryNamedLevelNoise_nativeBorel:BorelSpace CircleL2:=⟨rfl⟩
local instance ordinaryNamedLevelNoise_rowSigma:MeasurableSpace RealHaarInput:=borel _
local instance ordinaryNamedLevelNoise_rowBorel:BorelSpace RealHaarInput:=⟨rfl⟩
local instance ordinaryNamedLevelNoise_blockSigma:MeasurableSpace (Both RealHaarInput):=borel _
local instance ordinaryNamedLevelNoise_blockBorel:BorelSpace (Both RealHaarInput):=⟨rfl⟩
variable {Ω Y:Type}[MeasurableSpace Ω][MeasurableSpace Y]
variable {𝓕:Filtration ℝ≥0 ‹MeasurableSpace Ω›}{μ:Measure Ω}[IsProbabilityMeasure μ]
variable {H:ℝ≥0}{κ:ℝ}{a:ℝ→ℝ}{ell M:ℝ}(m:TwoChannelCutoffModel.Model 𝓕 μ H κ a ell M)
variable {R:ReferenceData}{n:ℕ}(L:Level R Y n)

/-- The ordinary rough-bracket noise version is exactly the named
original finite-Ito stochastic term, without a reference/actual match. -/
theorem noise_eq_original (hh:R.horizon≤(H:ℝ)){η:ℝ}(hη:0<η)
    (hgap:∀p i,η≤(L.observations.observations p i).target-L.terminal p)(p:Y):
    let b:ℝ≥0:=(L.terminal p).toNNReal
    let hb:(b:ℝ)=L.terminal p:=Real.coe_toNNReal _ (R.base_nonneg.trans (L.terminal_base p))
    let hbH:b≤H:=by exact_mod_cast (show (b:ℝ)≤H by rw [hb];exact (L.terminal_horizon p).trans hh)
    let hg:∀i,η≤(L.observations.observations p i).target-(b:ℝ):=by simpa only [hb] using hgap p
    OrdinaryUncutNoise.version m L p=ᵐ[μ] OrdinaryNamedIto.noise m
      (L.observations.observations p) b hη hg hbH R.base.toNNReal (backward (L.window p) (L.test p)):=by
  let b:ℝ≥0:=(L.terminal p).toNNReal
  have hb:(b:ℝ)=L.terminal p:=Real.coe_toNNReal _ (R.base_nonneg.trans (L.terminal_base p))
  have hbH:b≤H:=by exact_mod_cast (show (b:ℝ)≤H by rw [hb];exact (L.terminal_horizon p).trans hh)
  have hg:∀i,η≤(L.observations.observations p i).target-(b:ℝ):=by simpa only [hb] using hgap p
  let v:ℝ≥0:=R.base.toNNReal
  have hv:(v:ℝ)=R.base:=Real.coe_toNNReal _ R.base_nonneg
  have hvb:v≤b:=by exact_mod_cast (show (v:ℝ)≤(b:ℝ) by rw [hv,hb];exact L.terminal_base p)
  let N:=OrdinaryNamedIto.noise m (L.observations.observations p) b hη hg hbH v
  let D:=OrdinaryLevelOriginalNoise.data m L (fun _=>N)
  have hD:AnalyticConditions D:=by
    have hM:0≤M:=OrdinaryNamedIto.upper_nonneg m
    have hcap(z):|κ+a z|≤κ+M:=by
      rw [abs_of_nonneg (add_nonneg m.additive_pos.le (m.lower_pos.le.trans (m.variance_bounds z).1))]
      exact add_le_add le_rfl (m.variance_bounds z).2
    exact ActualVarianceLevel.analyticConditions L (fun z=>κ+a z) (measurable_const.add m.variance_measurable)
      m.physicalState m.physicalState_measurable m.physicalField m.physicalField_measurable (fun _=>N)
      (add_nonneg m.additive_pos.le hM) hcap
  have hF:=hD.tests_uniform.boundedSmooth p
  obtain ⟨C,hC⟩:=hF.norm_bound
  obtain ⟨B,hB⟩:=hF.fderiv.norm_bound
  obtain ⟨E,hE⟩:=hF.fderiv.fderiv.norm_bound
  obtain ⟨A,W,T,hA,hW,hT,hcap,hwin,hleft,hright⟩:=hD.bounds
  obtain ⟨K,hKn,hK⟩:=hF.hessian_lipschitz
  have hi:=OrdinaryNamedIto.finiteItoInput m (L.observations.observations p) b hη hg hbH v hvb
  rw [hb,hv] at hi
  have hs:=PhysicalIto.physical_one_step μ (L.window p) (fun z=>κ+a z) (measurable_const.add m.variance_measurable)
    (fun ω t=>m.physicalState (ω,t)) (fun ω q=>m.physicalField (ω,q))
    (Filter.Eventually.of_forall (PredictableScalarField.wordField_section_measurable 𝓕 m.state_predictable))
    hA hcap N hi (hF.smooth.of_le (by simp)) hC hB hE
    ((norm_nonneg _).trans (hE 0)) hKn hK
  filter_upwards [hs] with ω hω
  rw [←PhysicalIto.backward_eq_semigroup (L.window p) (D.test p) ⟨le_rfl,(L.window p).ordered⟩] at hω
  change D.leaf p ω=D.reference p ω+N (backward (L.window p) (L.test p)) ω+D.remainder p ω at hω
  change D.noiseVersion p ω=N (backward (L.window p) (L.test p)) ω
  dsimp only [LevelData.noiseVersion]
  linarith only [hω]

end SHE.OrdinaryNamedLevelNoise
