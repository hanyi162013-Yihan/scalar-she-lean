module

public import SHE.PastMeanSections
public import SHE.ScalarMassNormalization
public import SHE.QuarterSpatialEvent

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 2500000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHE.PastMeanEnvelope
open Set Filter MeasureTheory Real StoppedFourier CutoffWordLevel CutoffWordHistories
  CutoffCarriers PhysicalParentGeometry PhysicalScoreChain PhysicalChainArrays HistoryProductMeasure
  ActualMeanKernel ScalarMeanEnvelope NormalizedKernelSplit QuarterSpatialEvent HistoryQuarterFields
local instance pastMeanEnvelope_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
variable {R : ReferenceData} (L : Level R HeatCircle 1)

/-- The exact terminal heat age after the true later quarter row. -/
def width (T : ℝ) (k : ℕ) (q : ℝ) (t : Fin k→ℝ) : ℝ := T-quarterRowTime (R:=R) T k q t

def amplitude (P : CanonicalCovariance.ProfileParameters) (T : ℝ) (k : ℕ) (Λ q A0 ν : ℝ)
    (t : Fin k→ℝ) : ℝ :=
  PastMeanAmplitude.damped L P k Λ q A0 ν (anchor k t)*ScalarMeanEnvelope.massCoefficient k 1*
    width (R:=R) T k q t^(1/4:ℝ)

def envelope (P : CanonicalCovariance.ProfileParameters) (T : ℝ) (k : ℕ) (Λ q A0 ν : ℝ)
    (z : (Fin k→ℝ)×Space) : ℝ :=
  amplitude L P T k Λ q A0 ν z.1*
    ‖ProfileVariance.heatPhysical (8*width (R:=R) T k q z.1) z.2.1 z.2.2‖

theorem width_measurable (T : ℝ) (k : ℕ) (q : ℝ) : Measurable (width (R:=R) T k q) :=
  measurable_const.sub (quarterRowTime_measurable T k measurable_const measurable_id)

theorem amplitude_measurable (P : CanonicalCovariance.ProfileParameters) (T : ℝ) (k : ℕ) (Λ q A0 ν : ℝ) :
    Measurable (amplitude L P T k Λ q A0 ν) :=
  (((PastMeanAmplitude.damped_measurable L P k Λ q A0 ν).comp (anchor_measurable k)).mul_const _).mul
    ((width_measurable (R:=R) T k q).pow_const _)

theorem envelope_measurable (P : CanonicalCovariance.ProfileParameters) (T : ℝ) (k : ℕ) (Λ q A0 ν : ℝ) :
    Measurable (envelope L P T k Λ q A0 ν) := by
  have hm:=ProfileVariance.heatPhysical_joint_measurable.comp
    (((((width_measurable (R:=R) T k q).comp measurable_fst).const_mul 8).prodMk measurable_snd.fst).prodMk measurable_snd.snd)
  exact ((amplitude_measurable L P T k Λ q A0 ν).comp measurable_fst).mul hm.norm

theorem width_pos (T : ℝ) (hT : ∀ x,L.terminal x=T) (k : ℕ) (q : ℝ) (t : Fin k→ℝ)
    (hq : q<fixedTerminal (R:=R) T k t) : 0<width (R:=R) T k q t := by
  have hterm : fixedTerminal (R:=R) T k t≤T := by
    rw [←terminal_separated L T hT k t (0:HeatCircle) (fun _=>0)]
    simpa only [anchor,PhysicalScoreChain.initialTerminal,root_separated,hT] using terminal_le_initial L k (anchor k t)
  have hrow : quarterRowTime (R:=R) T k q t<fixedTerminal (R:=R) T k t := (quarter_geometry T k q t hq).2.2.1
  exact sub_pos.mpr (hrow.trans_le hterm)

theorem amplitude_nonneg (P : CanonicalCovariance.ProfileParameters) (T : ℝ) (hT : ∀ x,L.terminal x=T)
    (k : ℕ) (Λ q A0 ν : ℝ) (t : Fin k→ℝ) (hq : q<fixedTerminal (R:=R) T k t) :
    0≤amplitude L P T k Λ q A0 ν t :=
  mul_nonneg (mul_nonneg (PastMeanAmplitude.damped_nonneg L P k Λ q A0 ν _)
    (ScalarMeanEnvelope.massCoefficient_nonneg k zero_le_one)) (rpow_nonneg (width_pos L T hT k q t hq).le _)

/-- Exact p-eight normalization at the true later-row width. This
avoids a spatial supremum and introduces no heat-age comparison loss. -/
theorem mass_eq_envelope (P : CanonicalCovariance.ProfileParameters) (T : ℝ)
    (hT : ∀ x,L.terminal x=T)
    (htarget : ∀ x i,(L.observations.observations x i).target=T)
    (hcenter : ∀ x,(L.observations.observations x 0).center=x)
    (k : ℕ) (Λ q A0 ν : ℝ) (t : Fin k→ℝ) (x y : HeatCircle)
    (hq : q<fixedTerminal (R:=R) T k t) :
    let p:=separated k (x,t,fun _=>(0:HeatCircle))
    let r:=rowTime L k q p
    PastMeanAmplitude.damped L P k Λ q A0 ν p*massBudget L k p 1 r y=
      envelope L P T k Λ q A0 ν (t,(y,x)) := by
  intro p r
  have hD:=PastMeanAmplitude.damped_sections L P T hT (fun _=>T) htarget k t x 0 (fun _=>0) (fun _=>0) Λ q A0 ν
  have hr : r=quarterRowTime (R:=R) T k q t := rowTime_separated L T hT k q t x (fun _=>0)
  have hw:=width_pos L T hT k q t hq
  have hxroot : rootParameter k p=x := root_separated k (x,t,fun _=>0)
  rw [hD,massBudget_scalar L T (fun x=>htarget x 0) hcenter]
  simp only [hr,hxroot]
  rw [ProfileL2.heatPhysical_norm_symm (by change 0<8*width (R:=R) T k q t;positivity :
    0<8*(T-quarterRowTime (R:=R) T k q t)) x y]
  unfold envelope amplitude width
  dsimp only [anchor]
  ring

end SHE.PastMeanEnvelope
