module

public import SHE.GaussianStoppedRows
public import SHE.GaussianRowGramCurve

@[expose] public section
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SHE.GaussianDeterministicRows
open Set MeasureTheory ProbabilityTheory PredictableL2 GaussianMatrixGramCurve
open GaussianRowGramCurve GaussianStoppedRows SmoothCylinders GaussianConvolution
open scoped NNReal ENNReal
variable {Ω C : Type*} [MeasurableSpace Ω]
variable [NormedAddCommGroup C] [InnerProductSpace ℝ C] [CompleteSpace C]
variable [MeasurableSpace C] [BorelSpace C] [SecondCountableTopology C]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ]
variable (H v b : ℝ≥0) (hvb : v≤b) (hbH : b≤H)
variable {n : ℕ} (R : Fin n → Process (E:=C) 𝓕 μ H)
variable (r : Fin n → ℝ → C) (hr : ∀ i,Measurable (r i))
variable (hri : ∀ i,IntervalIntegrable (fun t=>‖r i t‖^2) volume (v:ℝ) b)
local notation "D" => GaussianRowGramCurve.density r hr (v:ℝ) (b:ℝ) (by exact_mod_cast hvb) hri
local notation "W" => GaussianMatrixGramCurve.curve D

include hbH in
/-- The bracket equality is derived from actual original-row equality
on the original energy measure, before the time/sample Fubini exchange. -/
theorem row_covariance
    (hdet : ∀ i,∀ᵐ p∂energyMeasure μ H,
      v<p.1 ∧ p.1<b → R i p=r i (p.1:ℝ)) :
    ∀ᵐ ω∂μ,∀ᵐ t:ℝ,t∈Ioo (v:ℝ) (b:ℝ) →
      StandardFiniteIto.rowCovariance 𝓕 μ H (GaussianStoppedRows.rows 𝓕 μ H v b R) ω t=
        gram r t := by
  have hp : ∀ᵐ p∂energyMeasure μ H,∀ i,
      v<p.1 ∧ p.1<b → GaussianStoppedRows.rows 𝓕 μ H v b R i p=r i (p.1:ℝ) := by
    filter_upwards [ae_all_iff.mpr (fun i=>GaussianStoppedRows.rows_ae 𝓕 μ H v b R i),
      ae_all_iff.mpr hdet] with p hs hd
    intro i hi
    rw [hs i,ite_eq_left hi]
    exact hd i hi
  have hs := (Measure.measurePreserving_swap (μ:=μ) (ν:=timeMeasure H)).quasiMeasurePreserving.ae hp
  filter_upwards [Measure.ae_ae_of_ae_prod hs] with ω hω
  have hre : ∀ᵐ t:ℝ∂volume.restrict (Ioc (0:ℝ) (H:ℝ)),t∈Ioo (v:ℝ) (b:ℝ) →
      StandardFiniteIto.rowCovariance 𝓕 μ H (GaussianStoppedRows.rows 𝓕 μ H v b R) ω t=gram r t := by
    rw [←timeMeasure_map H]
    apply nonnegative_coe_measurableEmbedding.ae_map_iff.mpr
    filter_upwards [hω] with t ht htin
    simp only [Prod.swap] at ht
    have hti : v<t ∧ t<b := by exact_mod_cast htin
    ext i j
    change inner ℝ (GaussianStoppedRows.rows 𝓕 μ H v b R i ((t:ℝ).toNNReal,ω))
      (GaussianStoppedRows.rows 𝓕 μ H v b R j ((t:ℝ).toNNReal,ω))=inner ℝ (r i (t:ℝ)) (r j (t:ℝ))
    simp only [Real.toNNReal_coe]
    rw [ht i hti,ht j hti]
  rw [ae_restrict_iff' measurableSet_Ioc] at hre
  filter_upwards [hre] with t ht htin
  exact ht ⟨v.2.trans_lt htin.1,htin.2.le.trans (by exact_mod_cast hbH)⟩ htin

variable (J : StandardTerminalIto (C:=C) (E:=ℝ) 𝓕 μ H) (z:WordRecursion.State n)

include hbH in
/-- Deterministic physical rows of the original integral have their
actual joint Gaussian conditional transition, including a singular
terminal heat age. No distribution of the stochastic integral is assumed. -/
theorem conditional_smooth (hb0:0<b)
    (hnull:NullCompleteFiltration.ContainsNullSets 𝓕 μ)
    (B:ℝ≥0)(hBDG:StandardTerminalBDG16 J B)
    (K:Fin n→ℝ)(hK:∀i,0≤K i)(hR:∀i,SingularInputBounds.Bound 𝓕 μ H b (K i) (R i))
    (hdet:∀i,∀ᵐp∂energyMeasure μ H,v<p.1 ∧ p.1<b→R i p=r i (p.1:ℝ))
    (hJ:StandardFiniteIto.Universal 𝓕 μ H J)(hlocal:StandardTerminalPastLocality J)
    {F:WordRecursion.State n→ℝ}(hF:BoundedSmooth F)(A:Set Ω)(hA:MeasurableSet[𝓕 v] A):
    (∫ω in A,F (GaussianStoppedRows.terminal 𝓕 μ H v b R J z ω) ∂μ)=
      μ.real A * gaussianAverage (GaussianMatrixGramCurve.covariance D v b) F z := by
  have he := GaussianStoppedRows.conditional_smooth 𝓕 μ H v b R J z hbH hb0 hnull B hBDG K hK hR
    hJ hlocal W rfl rfl (row_covariance (𝓕:=𝓕) (μ:=μ) (H:=H) (v:=v) (b:=b) (hbH:=hbH) (R:=R) (r:=r) hdet) hF A hA
  have hp : ((W).path (W).left).val=GaussianMatrixGramCurve.covariance D v b :=
    GaussianMatrixGramCurve.path_eq D ⟨le_rfl,by exact_mod_cast hvb⟩
  rwa [hp] at he

end SHE.GaussianDeterministicRows
