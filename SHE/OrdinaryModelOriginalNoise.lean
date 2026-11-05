module
public import SHE.TwoChannelCutoffModel
public import SHE.FiniteItoPastNoise
public import SHE.ActualVarianceLevel

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
namespace SHE.OrdinaryModelOriginalNoise
open Set MeasureTheory PredictableL2 FiniteHaar DyadicApproximation StoppedFourier
  NativeHeatObservation NativeObservationNaturality WordRecursion OrthogonalItoChannels
  CutoffWordLevel IntegratedPhysicalStep
open scoped NNReal ENNReal
local instance ordinaryModelOriginalNoise_realSigma:MeasurableSpace RealL2:=borel _
local instance ordinaryModelOriginalNoise_realBorel:BorelSpace RealL2:=⟨rfl⟩
local instance ordinaryModelOriginalNoise_rowSigma:MeasurableSpace RealHaarInput:=borel _
local instance ordinaryModelOriginalNoise_rowBorel:BorelSpace RealHaarInput:=⟨rfl⟩
local instance ordinaryModelOriginalNoise_blockSigma:MeasurableSpace (Both RealHaarInput):=borel _
local instance ordinaryModelOriginalNoise_blockBorel:BorelSpace (Both RealHaarInput):=⟨rfl⟩
variable {Ω:Type*}[MeasurableSpace Ω]
variable {𝓕:Filtration ℝ≥0 ‹MeasurableSpace Ω›}{μ:Measure Ω}[IsProbabilityMeasure μ]
variable {H:ℝ≥0}{κ:ℝ}{a:ℝ→ℝ}{ell M:ℝ}
variable (m:TwoChannelCutoffModel.Model 𝓕 μ H κ a ell M)

/-- Genuine pure-state physical Ito with the ACTUAL rough bracket and
the original two noise channels, centered on every event at the past. -/
theorem finiteItoInput (hlocal:StandardTerminalPastLocality m.scalarIto)
    {n:ℕ}(Z:Fin n→Observation)(b:ℝ≥0)(hb:b≤H)
    {δ:ℝ}(hδ:0<δ)(hgap:∀i,δ≤(Z i).target-(b:ℝ))
    (v:ℝ≥0)(hvb:v≤b):
    ∃N:(ℝ→WordRecursion.State n→ℝ)→Ω→ℝ,
      (∀G,Integrable (N G) μ ∧ ∀A,MeasurableSet[𝓕 v] A→(∫ω in A,N G ω ∂μ)=0) ∧
      (∀G,∃input:Process (E:=Both RealHaarInput) 𝓕 μ H,
        m.scalarIto.integral (PastItoInputs.post 𝓕 μ H v input)=ᵐ[μ] N G) ∧
      PhysicalIto.FiniteItoInput μ
        (fun ω=>observe (fun t=>m.physicalState (ω,t)) (fun p=>m.physicalField (ω,p)) Z)
        (fun ω t=>CovarianceMatrix.densityMatrix (fun p=>κ+a (m.physicalField (ω,p))) Z t) v b N:=by
  have hM:0≤M:=m.lower_pos.le.trans ((m.variance_bounds 0).1.trans (m.variance_bounds 0).2)
  let f₀:=fun _:ℝ≥0×Ω=>AdditiveHaarForcing.constantField κ m.additive_pos
  let Y:=LocalNativeObservations.stoppedValue δ Z m.state b
  let R:=LocalTwoChannelObservations.rows 𝓕 μ H m.additive_pos m.additive_pos.le f₀ stronglyMeasurable_const
    m.lower_pos hM m.coefficient m.coefficient_predictable Z b hδ hgap
  have hRep:=LocalTwoChannelObservations.integral_representation 𝓕 μ H m.additive_pos m.additive_pos.le
    f₀ stronglyMeasurable_const m.lower_pos hM m.coefficient m.coefficient_predictable Z b hδ hgap
    m.additiveIto m.residualIto m.scalarIto m.additive_naturality m.residual_naturality
    m.initial m.state m.additiveInput m.residualInput m.additive_kernel m.residual_kernel m.mild_identity hb
  have hY:=LocalTwoChannelObservations.predictable_of_representation (δ:=δ) 𝓕 μ H Z b
    m.null_complete m.scalarIto R (PositiveGapObservations.initial Z m.initial) m.state m.state_continuous hRep
  let N:(ℝ→WordRecursion.State n→ℝ)→Ω→ℝ:=fun G ω=>
    FiniteItoNoise.noise 𝓕 μ H Y hY R m.scalarIto v b G ω
  have hi:=StandardFiniteIto.finiteItoInput 𝓕 μ H m.scalarIto m.finiteIto R
    (PositiveGapObservations.initial Z m.initial) Y hY
    (fun ω=>LocalNativeObservations.stoppedValue_continuous δ Z m.state b (m.state_continuous ω))
    (fun t _=>hRep t) v.2 (by exact_mod_cast hvb) (by exact_mod_cast hb)
  have hd:=LocalTwoChannelIto.finiteItoInput_of_sum_density 𝓕 μ H m.additive_pos m.additive_pos.le
    f₀ stronglyMeasurable_const m.lower_pos hM m.coefficient m.coefficient_predictable Z b hδ hgap
    hb v.2 (by exact_mod_cast hvb) (fun ω t=>Y (t.toNNReal,ω)) N hi
  have hp:=NativeObservationIto.finiteItoInput_congr_path μ (by exact_mod_cast hvb) hd
    (fun ω t ht=>LocalNativeObservationIto.stoppedValue_eq_observe
      (Z:=Z) (b:=b) (hδ:=hδ) (hgap:=hgap) m.state
      (fun ω p=>m.physicalField (ω,p)) ω (v.2.trans ht.1) ht.2)
  have hpost(G:ℝ→WordRecursion.State n→ℝ):
      ∃input:Process (E:=Both RealHaarInput) 𝓕 μ H,
        m.scalarIto.integral (PastItoInputs.post 𝓕 μ H v input)=ᵐ[μ] N G:=by
    classical
    by_cases hG:FiniteItoNoise.AdmissibleGradient G
    · refine ⟨StoppedItoInputs.stop 𝓕 μ H (b:ℝ) (FiniteItoNoise.gradientProcess 𝓕 μ H Y hY R G hG),?_⟩
      have he:=FiniteItoPastNoise.noise_eq_post 𝓕 μ H Y hY R m.scalarIto v b hvb G hG
      exact Filter.Eventually.of_forall (fun ω=>congrFun (congrArg (fun f:Lp ℝ 2 μ=>fun ω=>f ω) he.symm) ω)
    · refine ⟨0,?_⟩
      have hz:PastItoInputs.post 𝓕 μ H v (0:Process (E:=Both RealHaarInput) 𝓕 μ H)=0:=by
        simpa only [sub_self] using PastItoAlgebra.post_sub 𝓕 μ H v
          (0:Process (E:=Both RealHaarInput) 𝓕 μ H) 0
      rw [hz,map_zero]
      dsimp only [N,FiniteItoNoise.noise]
      rw [dif_neg hG]
  refine ⟨N,fun G=>⟨FiniteItoNoise.noise_integrable 𝓕 μ H Y hY R m.scalarIto v b G,
    fun A hA=>FiniteItoPastNoise.noise_centered_on_past_event 𝓕 μ H Y hY R m.scalarIto hlocal v b hvb G A hA⟩,hpost,?_⟩
  intro G dG hG
  filter_upwards [hp G dG hG] with ω hω
  dsimp only [TwoChannelCutoffModel.Model.physicalState]
  rw [hω]
  congr 1
  apply intervalIntegral.integral_congr_Ioo_of_le (by exact_mod_cast hvb)
  intro t ht
  dsimp only [TwoChannelCutoffModel.Model.physicalField]
  rw [NonlinearTwoChannelStep.density_sum_eq 𝓕 κ m.additive_pos m.lower_pos m.coefficient m.state
    m.state_predictable a m.variance_measurable m.variance_bounds m.coefficient_identity Z hδ hgap ht.2.le ω]

end SHE.OrdinaryModelOriginalNoise
