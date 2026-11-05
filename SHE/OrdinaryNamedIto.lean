module
public import SHE.OrdinaryModelOriginalNoise

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
namespace SHE.OrdinaryNamedIto
open Set MeasureTheory PredictableL2 FiniteHaar DyadicApproximation StoppedFourier
  NativeHeatObservation NativeObservationNaturality WordRecursion OrthogonalItoChannels
open scoped NNReal ENNReal
local instance ordinaryNamedIto_realSigma:MeasurableSpace RealL2:=borel _
local instance ordinaryNamedIto_realBorel:BorelSpace RealL2:=⟨rfl⟩
local instance ordinaryNamedIto_rowSigma:MeasurableSpace RealHaarInput:=borel _
local instance ordinaryNamedIto_rowBorel:BorelSpace RealHaarInput:=⟨rfl⟩
local instance ordinaryNamedIto_blockSigma:MeasurableSpace (Both RealHaarInput):=borel _
local instance ordinaryNamedIto_blockBorel:BorelSpace (Both RealHaarInput):=⟨rfl⟩
variable {Ω:Type}[MeasurableSpace Ω]
variable {𝓕:Filtration ℝ≥0 ‹MeasurableSpace Ω›}{μ:Measure Ω}[IsProbabilityMeasure μ]
variable {H:ℝ≥0}{κ:ℝ}{a:ℝ→ℝ}{ell M:ℝ}(m:TwoChannelCutoffModel.Model 𝓕 μ H κ a ell M)

def upper_nonneg : 0≤M:=m.lower_pos.le.trans ((m.variance_bounds 0).1.trans (m.variance_bounds 0).2)
def additiveField:ℝ≥0×Ω→EllipticField κ κ:=fun _=>AdditiveHaarForcing.constantField κ m.additive_pos
def rows {n:ℕ}(Z:Fin n→Observation)(b:ℝ≥0){δ:ℝ}(hδ:0<δ)
    (hgap:∀i,δ≤(Z i).target-(b:ℝ)):Fin n→Process (E:=Both RealHaarInput) 𝓕 μ H:=
  LocalTwoChannelObservations.rows 𝓕 μ H m.additive_pos m.additive_pos.le (additiveField m) stronglyMeasurable_const
    m.lower_pos (upper_nonneg m) m.coefficient m.coefficient_predictable Z b hδ hgap

def path {n:ℕ}(δ:ℝ)(Z:Fin n→Observation)(b:ℝ≥0):ℝ≥0×Ω→WordRecursion.State n:=
  LocalNativeObservations.stoppedValue δ Z m.state b

theorem representation {n:ℕ}(Z:Fin n→Observation)(b:ℝ≥0){δ:ℝ}(hδ:0<δ)
    (hgap:∀i,δ≤(Z i).target-(b:ℝ))(hb:b≤H)(t:ℝ≥0):
    (fun ω=>path m δ Z b (t,ω))=ᵐ[μ]
      StandardFiniteIto.vectorIntegral 𝓕 μ H m.scalarIto (PositiveGapObservations.initial Z m.initial)
        (rows m Z b hδ hgap) t:=
  LocalTwoChannelObservations.integral_representation 𝓕 μ H m.additive_pos m.additive_pos.le
    (additiveField m) stronglyMeasurable_const m.lower_pos (upper_nonneg m) m.coefficient m.coefficient_predictable Z b hδ hgap
    m.additiveIto m.residualIto m.scalarIto m.additive_naturality m.residual_naturality
    m.initial m.state m.additiveInput m.residualInput m.additive_kernel m.residual_kernel m.mild_identity hb t

theorem path_predictable {n:ℕ}(Z:Fin n→Observation)(b:ℝ≥0){δ:ℝ}(hδ:0<δ)
    (hgap:∀i,δ≤(Z i).target-(b:ℝ))(hb:b≤H):
    StronglyMeasurable[𝓕.predictable] (path m δ Z b):=
  LocalTwoChannelObservations.predictable_of_representation (δ:=δ) 𝓕 μ H Z b
    m.null_complete m.scalarIto (rows m Z b hδ hgap) (PositiveGapObservations.initial Z m.initial)
    m.state m.state_continuous (representation m Z b hδ hgap hb)

def noise {n:ℕ}(Z:Fin n→Observation)(b:ℝ≥0){δ:ℝ}(hδ:0<δ)
    (hgap:∀i,δ≤(Z i).target-(b:ℝ))(hb:b≤H)(v:ℝ≥0)(G:ℝ→WordRecursion.State n→ℝ):Ω→ℝ:=
  FiniteItoNoise.noise 𝓕 μ H (path m δ Z b) (path_predictable m Z b hδ hgap hb)
    (rows m Z b hδ hgap) m.scalarIto v b G

/-- Explicit finite-Ito noise, with the actual rough total bracket;
the witness is named so its literal gradient input can be retained. -/
theorem finiteItoInput {n:ℕ}(Z:Fin n→Observation)(b:ℝ≥0){δ:ℝ}(hδ:0<δ)
    (hgap:∀i,δ≤(Z i).target-(b:ℝ))(hb:b≤H)(v:ℝ≥0)(hvb:v≤b):
    PhysicalIto.FiniteItoInput μ
      (fun ω=>observe (fun t=>m.physicalState (ω,t)) (fun p=>m.physicalField (ω,p)) Z)
      (fun ω t=>CovarianceMatrix.densityMatrix (fun p=>κ+a (m.physicalField (ω,p))) Z t) v b
      (noise m Z b hδ hgap hb v):=by
  let Y:=path m δ Z b
  let R:=rows m Z b hδ hgap
  let hY:=path_predictable m Z b hδ hgap hb
  let N:=noise m Z b hδ hgap hb v
  have hi:=StandardFiniteIto.finiteItoInput 𝓕 μ H m.scalarIto m.finiteIto R
    (PositiveGapObservations.initial Z m.initial) Y hY
    (fun ω=>LocalNativeObservations.stoppedValue_continuous δ Z m.state b (m.state_continuous ω))
    (fun t _=>representation m Z b hδ hgap hb t) v.2 (by exact_mod_cast hvb) (by exact_mod_cast hb)
  have hd:=LocalTwoChannelIto.finiteItoInput_of_sum_density 𝓕 μ H m.additive_pos m.additive_pos.le
    (additiveField m) stronglyMeasurable_const m.lower_pos (upper_nonneg m) m.coefficient m.coefficient_predictable Z b hδ hgap
    hb v.2 (by exact_mod_cast hvb) (fun ω t=>Y (t.toNNReal,ω)) N hi
  have hp:=NativeObservationIto.finiteItoInput_congr_path μ (by exact_mod_cast hvb) hd
    (fun ω t ht=>LocalNativeObservationIto.stoppedValue_eq_observe
      (Z:=Z) (b:=b) (hδ:=hδ) (hgap:=hgap) m.state
      (fun ω p=>m.physicalField (ω,p)) ω (v.2.trans ht.1) ht.2)
  intro G dG hG
  filter_upwards [hp G dG hG] with ω hω
  dsimp only [TwoChannelCutoffModel.Model.physicalState]
  rw [hω]
  congr 1
  apply intervalIntegral.integral_congr_Ioo_of_le (by exact_mod_cast hvb)
  intro t ht
  dsimp only [TwoChannelCutoffModel.Model.physicalField]
  unfold additiveField
  rw [NonlinearTwoChannelStep.density_sum_eq 𝓕 κ m.additive_pos m.lower_pos m.coefficient m.state
    m.state_predictable a m.variance_measurable m.variance_bounds m.coefficient_identity Z hδ hgap ht.2.le ω]

end SHE.OrdinaryNamedIto
