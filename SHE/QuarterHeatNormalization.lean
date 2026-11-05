module

public import SHE.ScalarMassNormalization
public import SHE.HistoryQuarterFields

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency true
noncomputable section

namespace SHE.NormalizedKernelSplit
open Real StoppedFourier
local instance quarterHeatNormalization_nativePositive : Fact (0 < 2*Real.pi) := ⟨by positivity⟩

/-- The actual periodic heat envelope tolerates the quarter-split width
change with a fixed factor. Both the quarter power and the spatial heat
kernel retain their true ages. -/
theorem heatEnvelope_comparable {D δ s t : ℝ} (hD : 0 ≤ D) (hδ : 0 ≤ δ)
    (hs : 0 < s) (hst : s ≤ t) (hts : t ≤ 2*s) (p : Space) :
    heatEnvelope D δ s p ≤ heatEnvelope (sqrt 2*D) δ t p := by
  have hp : s^(1/4:ℝ) ≤ t^(1/4:ℝ) :=
    Real.rpow_le_rpow hs.le hst (by norm_num)
  have hk := NativeHeatSpan.physical_comparable
    (by positivity : 0 < 8*s) (by linarith : 8*s ≤ 8*t)
    (by linarith : 8*t ≤ 2*(8*s)) p.1 p.2
  have ha : 0 ≤ D*δ^(-(1/2:ℝ)) := mul_nonneg hD (Real.rpow_nonneg hδ _)
  unfold heatEnvelope heatAmplitude
  calc
    _ ≤ D*δ^(-(1/2:ℝ))*t^(1/4:ℝ)*
        (sqrt 2*‖ProfileVariance.heatPhysical (8*t) p.1 p.2‖) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hp ha) hk (norm_nonneg _)
        (mul_nonneg ha (Real.rpow_nonneg (hs.trans_le hst).le _))
    _ = _ := by ring

end SHE.NormalizedKernelSplit

namespace SHE.ScalarMeanEnvelope
open Real StoppedFourier CutoffWordLevel CutoffWordHistories
  NormalizedKernelSplit ActualMeanKernel HistoryProductMeasure CutoffCarriers PhysicalParentGeometry PhysicalScoreChain
local instance quarterMassNormalization_nativePositive : Fact (0 < 2*Real.pi) := ⟨by positivity⟩
variable {R : ReferenceData}
variable (L : CutoffWordLevel.Level R HeatCircle 1)

/-- Exact cancellation of the terminal first-score inverse square root
against the normalization of the retained right-hand heat operator. -/
theorem quarter_fresh_cancel {Cf ell g : ℝ} (hCf : 0 ≤ Cf) (hell : 0 < ell)
    (hg : 0 < g) :
    sqrt (Cf/(ell*(3*g/4)))*(g/2)^(1/2:ℝ)=sqrt (2*Cf/(3*ell)) := by
  rw [←Real.sqrt_eq_rpow,←Real.sqrt_mul (by positivity : 0 ≤ Cf/(ell*(3*g/4)))]
  congr 1
  field_simp
  ring

/-- The deterministic amplitude after the quarter split has no inverse
fresh gap. All old root clips and rough-block gains remain in D and W. -/
def quarterAmplitude (k : ℕ) (Cf ell D W : ℝ) : ℝ :=
  sqrt 2*sqrt (2*Cf/(3*ell))*D*massCoefficient k W

theorem quarterAmplitude_nonneg (k : ℕ) {Cf ell D W : ℝ}
    (hD : 0 ≤ D) (hW : 0 ≤ W) : 0 ≤ quarterAmplitude k Cf ell D W :=
  mul_nonneg (mul_nonneg (mul_nonneg (sqrt_nonneg _) (sqrt_nonneg _)) hD)
    (massCoefficient_nonneg k hW)

/-- The literal scalar old-space mass, including the fresh insertion
factor, is dominated by the original-width normalized heat envelope.
The common Gaussian covariance and current mean remain at q. -/
theorem quarter_massBudget_bound (T A : ℝ) (hT : ∀ p,L.terminal p=T)
    (hA : ∀ p,(L.observations.observations p 0).target=A)
    (hx : ∀ p,(L.observations.observations p 0).center=p)
    (k : ℕ) (q : ℝ) (t : Fin k → ℝ) (p y : HeatCircle)
    (hq : q < fixedTerminal (R:=R) T k t)
    (hTA : fixedTerminal (R:=R) T k t ≤ A)
    (Cf ell D W : ℝ) (hCf : 0 ≤ Cf) (hell : 0 < ell) (hD : 0 ≤ D) (hW : 0 ≤ W) :
    let r := quarterRowTime (R:=R) T k q t
    let δ := quarterTraceTime (R:=R) T k q t
    let p₀ := separated k (p,t,fun _ => (0:HeatCircle))
    (sqrt (Cf/(ell*((carrier L k).terminal p₀-r)))*D)*massBudget L k p₀ W r y ≤
      heatEnvelope (quarterAmplitude k Cf ell D W) δ (A-q) (y,p) := by
  intro r δ p₀
  obtain ⟨hg,_,_,hδ,_,_⟩ := quarter_geometry (R:=R) T k q t hq
  obtain ⟨hs,hst,hts,_⟩ := quarter_widths (R:=R) hq hTA
  have hgap : (carrier L k).terminal p₀-r=3*(fixedTerminal (R:=R) T k t-q)/4 := by
    simp only [p₀,terminal_separated L T hT,r,quarterRowTime,hg]
    ring
  have htrace : δ=(fixedTerminal (R:=R) T k t-q)/2 := by
    simp only [δ,quarterTraceTime,hg]
  have hcancel : sqrt (Cf/(ell*((carrier L k).terminal p₀-r)))*δ^(1/2:ℝ)=
      sqrt (2*Cf/(3*ell)) := by
    rw [hgap,htrace]
    exact quarter_fresh_cancel hCf hell (sub_pos.mpr hq)
  have hn : 0 ≤ (sqrt (Cf/(ell*((carrier L k).terminal p₀-r)))*D)*
      massCoefficient k W*δ^(1/2:ℝ) := by
    exact mul_nonneg (mul_nonneg (mul_nonneg (sqrt_nonneg _) hD)
      (massCoefficient_nonneg k hW)) (Real.rpow_nonneg hδ.le _)
  rw [massBudget_heatEnvelope L A hA hx k p₀ W
    (sqrt (Cf/(ell*((carrier L k).terminal p₀-r)))*D) r δ hδ hs y]
  have hb := heatEnvelope_comparable (δ:=δ) hn hδ.le hs hst hts (y,rootParameter k p₀)
  have he : sqrt 2*((sqrt (Cf/(ell*((carrier L k).terminal p₀-r)))*D)*
      massCoefficient k W*δ^(1/2:ℝ))=quarterAmplitude k Cf ell D W := by
    unfold quarterAmplitude
    calc
      _ = sqrt 2*(sqrt (Cf/(ell*((carrier L k).terminal p₀-r)))*δ^(1/2:ℝ))*D*massCoefficient k W := by ring
      _ = _ := by rw [hcancel]
  simpa only [he,p₀,root_separated,r] using hb

end SHE.ScalarMeanEnvelope
