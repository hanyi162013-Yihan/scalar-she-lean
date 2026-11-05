module
public import SHE.OriginalNativeWhiteHeatRows
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
set_option linter.unusedSectionVars false
namespace SHE.OriginalNativeWhiteHeatRows
open MeasureTheory Set PredictableL2 StoppedFourier DyadicApproximation FiniteHaar Filter
open scoped NNReal ENNReal Topology
local instance whiteHeatContinuity_unit : Fact (0<(1:ℝ)):=⟨zero_lt_one⟩
local instance whiteHeatContinuity_realSigma : MeasurableSpace RealL2:=borel _
local instance whiteHeatContinuity_realBorel : BorelSpace RealL2:=⟨rfl⟩
local instance whiteHeatContinuity_rowSigma : MeasurableSpace RealHaarInput:=borel _
local instance whiteHeatContinuity_rowBorel : BorelSpace RealHaarInput:=⟨rfl⟩
variable{Ω:Type*}[MeasurableSpace Ω]
variable(D:SmoothApproximation.ScalarData)(U:ℝ≥0→Ω→RealL2)

/-- The moving observation cutoff has only its single null time as a
possible discontinuity. All physical heat parameters are retained. -/
theorem raw_tendsto (q:ℝ≥0)(ε:ℝ)(hε:0<ε)(x:HeatCircle)
    (qn:ℕ→ℝ≥0)(en:ℕ→ℝ)(xn:ℕ→HeatCircle)
    (hq:Tendsto qn atTop (𝓝 q))(he:Tendsto en atTop (𝓝 ε))(hx:Tendsto xn atTop (𝓝 x))
    (p:ℝ≥0×Ω)(hp:p.1≠q):
    Tendsto (fun n=>raw D U (qn n) (en n) (xn n) p) atTop (𝓝 (raw D U q ε x p)):=by
  by_cases hr:p.1<q
  · have hn:∀ᶠn in atTop,p.1<qn n:=hq.eventually (eventually_gt_nhds hr)
    have hqr:Tendsto (fun n=>(qn n:ℝ)) atTop (𝓝 (q:ℝ)):=
      (continuous_subtype_val.tendsto q).comp hq
    have ha:Tendsto (fun n=>(qn n:ℝ)+en n-(p.1:ℝ)) atTop (𝓝 ((q:ℝ)+ε-(p.1:ℝ))):=
      (hqr.add he).sub_const _
    have hage:0<(q:ℝ)+ε-(p.1:ℝ):=by
      have hh:(p.1:ℝ)<q:=by exact_mod_cast hr
      linarith
    have hpar:Tendsto (fun n=>(((qn n:ℝ)+en n-(p.1:ℝ),xn n),U p.1 p.2)) atTop
        (𝓝 (((q:ℝ)+ε-(p.1:ℝ),x),U p.1 p.2)):=
      (ha.prodMk_nhds hx).prodMk_nhds tendsto_const_nhds
    have hi: Tendsto (fun n=>OriginalScalarInputContinuity.input D (U p.1 p.2)
        (ScalarHaarHeatRows.test ((qn n:ℝ)+en n-(p.1:ℝ)) (xn n))) atTop
        (𝓝 (OriginalScalarInputContinuity.input D (U p.1 p.2)
          (ScalarHaarHeatRows.test ((q:ℝ)+ε-(p.1:ℝ)) x))):=
      by simpa only[Function.comp_def] using
        (OriginalNativeHeatParameterContinuity.input_joint D hage x (U p.1 p.2)).tendsto.comp hpar
    have ht:=OriginalNativeFrozenRows.coordinates.symm.continuous.tendsto _ |>.comp hi
    rw[raw,ite_eq_left hr]
    apply ht.congr'
    filter_upwards[hn] with n hn
    simp only[Function.comp_def,raw,ite_eq_left hn,OriginalNativeRowContinuity.row]
  · have hrq:q<p.1:=lt_of_le_of_ne (le_of_not_gt hr) hp.symm
    have hn:∀ᶠn in atTop,qn n<p.1:=hq.eventually (eventually_lt_nhds hrq)
    rw[raw,ite_eq_right hr]
    apply (tendsto_const_nhds (x:=(0:RealHaarInput))).congr'
    filter_upwards[hn] with n hn
    simp only[raw,ite_eq_right (not_lt.mpr hn.le)]

/-- A strictly positive lower heat gap controls all centers, states and
observation cutoffs by one genuine original-row norm bound. -/
theorem raw_uniform_bound(q:ℝ≥0)(ε d:ℝ)(hd:0<d)(hde:d≤ε)(x:HeatCircle)(p:ℝ≥0×Ω):
    ‖raw D U q ε x p‖≤Real.sqrt (D.upper^2*(1+heatConstant*d^(-(1/2:ℝ)))):=by
  have hp:ε^(-(1/2:ℝ))≤d^(-(1/2:ℝ)):=
    Real.rpow_le_rpow_of_nonpos hd hde (by norm_num)
  have hb:=raw_norm_le D U q ε (hd.trans_le hde) x p
  have he:(q:ℝ)+ε-(q:ℝ)=ε:=by ring
  unfold OriginalNativeFrozenRows.bound at hb
  rw[he] at hb
  exact hb.trans (Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left
    (add_le_add le_rfl (mul_le_mul_of_nonneg_left hp heatConstant_pos.le)) (sq_nonneg _)))

variable(𝓕:Filtration ℝ≥0 ‹MeasurableSpace Ω›)(hU:IsStronglyPredictable 𝓕 U)
variable(μ:Measure Ω)[IsFiniteMeasure μ](H:ℝ≥0)

/-- Genuine Process-L2 continuity of the actual original before-q rows.
The only exceptional current time is q itself, which has zero time mass. -/
theorem input_tendsto (q:ℝ≥0)(ε:ℝ)(hε:0<ε)(x:HeatCircle)
    (qn:ℕ→ℝ≥0)(en:ℕ→ℝ)(hnpos:∀n,0<en n)(xn:ℕ→HeatCircle)
    (hq:Tendsto qn atTop (𝓝 q))(he:Tendsto en atTop (𝓝 ε))(hx:Tendsto xn atTop (𝓝 x)):
    Tendsto (fun n=>input D U 𝓕 hU μ H (qn n) (en n) (hnpos n) (xn n)) atTop
      (𝓝 (input D U 𝓕 hU μ H q ε hε x)):=by
  let f:=input D U 𝓕 hU μ H q ε hε x
  let fn:=fun n=>input D U 𝓕 hU μ H (qn n) (en n) (hnpos n) (xn n)
  let d:=ε/2
  have hd:0<d:=by dsimp[d];positivity
  let M:=Real.sqrt (D.upper^2*(1+heatConstant*d^(-(1/2:ℝ))))
  have hM:0≤M:=Real.sqrt_nonneg _
  haveI hfin:IsFiniteMeasure (energyMeasure μ H):=by unfold energyMeasure;infer_instance
  have hdiff(n:ℕ):(fun p:ℝ≥0×Ω=>‖fn n p-f p‖^2)=ᵐ[energyMeasure μ H]
      (fun p=>‖raw D U (qn n) (en n) (xn n) p-raw D U q ε x p‖^2):=by
    filter_upwards[input_ae D U 𝓕 hU μ H (qn n) (en n) (hnpos n) (xn n),
      input_ae D U 𝓕 hU μ H q ε hε x] with p hn hf
    rw[hn,hf]
  have hm(n:ℕ):AEStronglyMeasurable (fun p=>‖raw D U (qn n) (en n) (xn n) p-raw D U q ε x p‖^2)
      (energyMeasure μ H):=
    (((realization_stronglyMeasurable (energyMeasure μ H) (predictable_le_product 𝓕) (fn n)).sub
      (realization_stronglyMeasurable (energyMeasure μ H) (predictable_le_product 𝓕) f)).norm.pow 2).aestronglyMeasurable.congr (hdiff n)
  have hevent:∀ᶠn in atTop,d≤en n:=
    (he.eventually (eventually_gt_nhds (show d<ε by dsimp[d];linarith))).mono (fun _ hn=>hn.le)
  have hbound:∀ᶠn in atTop,∀ᵐp∂energyMeasure μ H,
      ‖‖raw D U (qn n) (en n) (xn n) p-raw D U q ε x p‖^2‖≤(2*M)^2:=by
    filter_upwards[hevent] with n hn
    apply ae_of_all
    intro p
    rw[Real.norm_of_nonneg (sq_nonneg _)]
    apply pow_le_pow_left₀ (norm_nonneg _)
    have h1:=raw_uniform_bound D U (qn n) (en n) d hd hn (xn n) p
    have h0:=raw_uniform_bound D U q ε d hd (by dsimp[d];linarith) x p
    have hh:‖raw D U (qn n) (en n) (xn n) p‖ + ‖raw D U q ε x p‖ ≤ 2*M:=by
      change ‖raw D U (qn n) (en n) (xn n) p‖≤M at h1
      change ‖raw D U q ε x p‖≤M at h0
      linarith
    exact (norm_sub_le _ _).trans hh
  have hnull:∀ᵐp:ℝ≥0×Ω∂energyMeasure μ H,p.1≠q:=
    Measure.quasiMeasurePreserving_fst.ae ((timeMeasure H).ae_ne q)
  have hlim:∀ᵐp∂energyMeasure μ H,Tendsto
      (fun n=>‖raw D U (qn n) (en n) (xn n) p-raw D U q ε x p‖^2) atTop (𝓝 (0:ℝ)):=by
    filter_upwards[hnull] with p hp
    have ht:=((raw_tendsto D U q ε hε x qn en xn hq he hx p hp).sub_const (raw D U q ε x p)).norm.pow 2
    simpa only[sub_self,norm_zero,zero_pow (by norm_num:(2:ℕ)≠0)] using ht
  have henergy:=tendsto_integral_filter_of_dominated_convergence (fun _p:ℝ≥0×Ω=>(2*M)^2)
    (Filter.Eventually.of_forall hm) hbound (integrable_const _) hlim
  have hnorm(n:ℕ):‖fn n-f‖^2=∫p,‖raw D U (qn n) (en n) (xn n) p-raw D U q ε x p‖^2 ∂energyMeasure μ H:=by
    rw[subsigma_norm_sq]
    apply integral_congr_ae
    filter_upwards[ae_eq_of_ae_eq_trim (Lp.coeFn_sub (fn n) f),hdiff n] with p hs hp
    rw[hs]
    exact hp
  have hsq:Tendsto (fun n=>‖fn n-f‖^2) atTop (𝓝 (0:ℝ)):=by
    simpa only[hnorm,integral_zero] using henergy
  rw[tendsto_iff_norm_sub_tendsto_zero]
  simpa only[Real.sqrt_sq (norm_nonneg _),Real.sqrt_zero] using hsq.sqrt
end SHE.OriginalNativeWhiteHeatRows
