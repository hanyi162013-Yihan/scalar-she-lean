module

public import SHE.PredictableScalarField
public import SHEStochastic.MeasurableHilbertL2Realization

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1800000
noncomputable section

namespace SHEStochastic.ScalarLinearGrowthDriftField
open MeasureTheory SHE SHE.FiniteHaar SHE.DyadicApproximation AddCircle
open scoped ENNReal NNReal

local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by simp⟩
local instance : SecondCountableTopology CircleHeat.CircleL2 :=
  (_root_.fourierBasis (T := (1 : ℝ))).repr.toHomeomorph.secondCountableTopology
local instance : SecondCountableTopology RealL2 := realCircleIdentification.toHomeomorph.secondCountableTopology
local instance : MeasurableSpace RealL2 := borel _
local instance : BorelSpace RealL2 := ⟨rfl⟩

abbrev Circle := AddCircle (1 : ℝ)
local notation "ν" => (haarAddCircle (T := (1 : ℝ)))

/-- The manuscript's Borel scalar drift and its linear growth bound on
one fixed physical horizon. -/
structure Data (H : ℝ≥0) where
  value : ℝ≥0×(Circle×ℝ)→ℝ
  measurable : Measurable value
  growth : ℝ≥0
  bound : ∀ t≤H,∀ x z,|value (t,(x,z))|≤(growth : ℝ)*(1+|z|)

variable {H : ℝ≥0} (b : Data H)

/-- The joint spatial field uses the Borel L² representative at every
state. The time argument agrees with the given drift throughout the horizon. -/
def evaluate (p : (ℝ≥0×RealL2)×Circle) : ℝ :=
  b.value (min p.1.1 H,(p.2,PredictableScalarField.unitField (id : RealL2→RealL2) (p.1.2,p.2)))

theorem evaluate_measurable : Measurable (evaluate b) :=
  b.measurable.comp
    ((measurable_fst.fst.min measurable_const).prodMk (measurable_snd.prodMk
      ((PredictableScalarField.unitField_measurable measurable_id).comp (measurable_fst.snd.prodMk measurable_snd))))

theorem evaluate_bound (p : ℝ≥0×RealL2) :
    ∀ᵐ x ∂ν, ‖evaluate b (p,x)‖≤(b.growth : ℝ)*(1+‖p.2 x‖) := by
  filter_upwards [PredictableScalarField.unitField_ae (id : RealL2→RealL2) p.2] with x hx
  unfold evaluate
  rw [Real.norm_eq_abs,hx,Real.norm_eq_abs]
  exact b.bound _ (min_le_right _ _) _ _

theorem evaluate_memLp (p : ℝ≥0×RealL2) : MemLp (fun x => evaluate b (p,x)) 2 ν := by
  have hM : MemLp (fun x => (b.growth : ℝ)*(1+‖p.2 x‖)) 2 ν :=
    ((memLp_const (1 : ℝ)).add (Lp.memLp p.2).norm).const_mul _
  exact hM.mono' ((evaluate_measurable b).comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
    (evaluate_bound b p)

/-- The actual drift as an L²-valued function of time and state. -/
def field (p : ℝ≥0×RealL2) : RealL2 :=
  (evaluate_memLp b p).toLp (fun x => evaluate b (p,x))

theorem field_ae (p : ℝ≥0×RealL2) :
    field b p =ᵐ[ν] fun x => b.value (min p.1 H,(x,p.2 x)) := by
  filter_upwards [(evaluate_memLp b p).coeFn_toLp,
    PredictableScalarField.unitField_ae (id : RealL2→RealL2) p.2] with x hx hr
  change field b p x = _ at hx
  rw [hx,evaluate,hr]
  rfl

theorem field_measurable : Measurable (field b) :=
  MeasurableHilbertL2Realization.measurable (evaluate b) (evaluate_measurable b) (field b)
    (fun p => (evaluate_memLp b p).coeFn_toLp)

private theorem norm_sq_of_bound (f v : RealL2) (L : ℝ≥0)
    (hb : ∀ᵐ x ∂ν, ‖f x‖ ≤ (L : ℝ)*(1+‖v x‖)) :
    ‖f‖^2≤2*(L : ℝ)^2*(1+‖v‖^2) := by
  have hIdentity (w : RealL2) : ‖w‖^2=∫ x,‖w x‖^2 ∂ν := by
    simpa only [real_inner_self_eq_norm_sq] using (L2.inner_def (𝕜 := ℝ) w w)
  have hBound : ∀ᵐ x ∂ν, ‖f x‖^2≤2*(L : ℝ)^2*(1+‖v x‖^2) := by
    filter_upwards [hb] with x hx
    calc
      _ ≤ ((L : ℝ)*(1+‖v x‖))^2 := pow_le_pow_left₀ (norm_nonneg _) hx 2
      _ ≤ _ := by nlinarith [mul_nonneg (sq_nonneg (L : ℝ)) (sq_nonneg (‖v x‖-1))]
  have hI : Integrable (fun x => ‖v x‖^2) ν := (Lp.memLp v).norm.integrable_sq
  have hD : Integrable (fun x => 2*(L : ℝ)^2*(1+‖v x‖^2)) ν :=
    (((integrable_const (1 : ℝ)).add hI).const_mul _)
  calc
    ‖f‖^2 = (∫ x, ‖f x‖^2 ∂ν) := hIdentity f
    _ ≤ ∫ x,2*(L : ℝ)^2*(1+‖v x‖^2) ∂ν :=
      integral_mono_ae (Lp.memLp f).norm.integrable_sq hD hBound
    _ = 2*(L : ℝ)^2*(1+‖v‖^2) := by
      rw [integral_const_mul,integral_add (integrable_const _) hI,←hIdentity v]
      simp

theorem field_norm_sq_le (p : ℝ≥0×RealL2) :
    ‖field b p‖^2≤2*(b.growth : ℝ)^2*(1+‖p.2‖^2) := by
  apply norm_sq_of_bound
  filter_upwards [(evaluate_memLp b p).coeFn_toLp,evaluate_bound b p] with x hx hb
  exact (congrArg norm hx).le.trans hb

/-- Divide by a Borel diffusion bounded away from zero, using its
absolute lower bound in the new linear-growth constant. -/
def divideBy (g : ℝ→ℝ) (hm : Measurable g) (c : ℝ≥0) (hc : 0<c) (hg : ∀ z,(c : ℝ)≤|g z|) :
    Data H where
  value p := b.value p / g p.2.2
  measurable := b.measurable.div (hm.comp measurable_snd.snd)
  growth := b.growth / c
  bound t ht x z := by
    rw [abs_div,NNReal.coe_div,div_mul_eq_mul_div]
    have hp : 0 < |g z| := (show 0<(c : ℝ) from hc).trans_le (hg z)
    exact (div_le_div_of_nonneg_right (b.bound t ht x z) hp.le).trans
      (div_le_div_of_nonneg_left (by positivity) (show 0<(c : ℝ) from hc) (hg z))

end SHEStochastic.ScalarLinearGrowthDriftField
