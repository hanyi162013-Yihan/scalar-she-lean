module

public import SHE.StoppedScoreTransfer

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
noncomputable section

namespace SHE.StoppedScoreLeverage
open Set MeasureTheory AddCircle Finset StoppedFourier StoppedGaussianFeatures GaussianAudit
  GaussianGramScore GaussianIncrement MeasurableGaussianScores ProfileL2
  GaussianWordCovarianceBound StoppedCovarianceInput
open scoped InnerProductSpace
local instance stoppedScoreL2_periodPos : Fact (0 < 2*Real.pi) := ⟨by positivity⟩
variable {n : ℕ} (σ target : Fin n → ℝ) (center : Fin n → HeatCircle)

def referenceConvolution (hages : ∀ i,σ i ≤ target i) (ell : ℝ) (e : Domain → ℝ)
    (x : HeatCircle) : ℝ :=
  ∫ p : Domain,(referenceKernel σ target center hages 0 p/ell)*|e (p.1,x+p.2)| ∂historyMeasure 0

def scoreInput (c e : Domain → ℝ) (x : HeatCircle) : ℝ :=
  ∫ p,|e p| * scoreVariance
    (StoppedGaussianFeatures.stoppedCovariance σ target (fun i => center i+x) c 0)
    (stoppedRow σ target (fun i => center i+x) p) ∂historyMeasure 0

theorem referenceConvolution_measurable (hages : ∀ i,σ i ≤ target i) (ell : ℝ)
    (e : Domain → ℝ) (he : Measurable e) :
    Measurable (referenceConvolution σ target center hages ell e) := by
  have hk := (physicalLeverage_properties
    (referenceCoefficients σ target center hages 0) σ target center hages).1
  have hF : Measurable (fun p : Domain × HeatCircle =>
      (referenceKernel σ target center hages 0 p.1/ell)*|e (p.1.1,p.2+p.1.2)|) :=
    ((hk.div_const ell).comp measurable_fst).mul
      ((continuous_abs.measurable.comp he).comp
        (measurable_fst.fst.prodMk (measurable_snd.add measurable_fst.snd)))
  exact hF.stronglyMeasurable.integral_prod_left'.measurable

theorem referenceConvolution_nonneg (hages : ∀ i,σ i ≤ target i) {ell : ℝ} (hell : 0 < ell)
    (e : Domain → ℝ) (x : HeatCircle) : 0 ≤ referenceConvolution σ target center hages ell e x := by
  apply integral_nonneg
  intro p
  exact mul_nonneg (div_nonneg ((physicalLeverage_properties
    (referenceCoefficients σ target center hages 0) σ target center hages).2.1 p) hell.le) (abs_nonneg _)

theorem referenceConvolution_bound (hages : ∀ i,σ i ≤ target i)
    {s τ ell L : ℝ} (hs : 0 < s) (hτ : -1 < τ) (hτ0 : τ ≤ 0)
    (hell : 0 < ell) (hL : 0 ≤ L) (hstop : ∀ i,s ≤ σ i)
    (e : Domain → ℝ) (he : Measurable e)
    (hcoarse : ∀ p,0 ≤ p.1 → |e p| ≤ L*p.1^τ) (x : HeatCircle) :
    referenceConvolution σ target center hages ell e x ≤
      L*(((n:ℝ)/ell)*(s/2)^τ*(1+2/(τ+1))) := by
  have href := referenceKernel_power_mass σ target center hages hs hτ hτ0 hstop
  have hi := reference_input_integrable σ target center hages hs hτ hτ0 hell hstop e he hcoarse x
  have hle : ∀ᵐ p ∂historyMeasure 0,(referenceKernel σ target center hages 0 p/ell)*|e (p.1,x+p.2)| ≤
      (L/ell)*(p.1^τ*referenceKernel σ target center hages 0 p) := by
    have ht : ∀ᵐ p : Domain ∂historyMeasure 0,0 ≤ p.1 :=
      Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem measurableSet_Ici)
    filter_upwards [ht] with p hp
    have hk0 : 0 ≤ referenceKernel σ target center hages 0 p :=
      (physicalLeverage_properties (referenceCoefficients σ target center hages 0) σ target center hages).2.1 p
    exact (mul_le_mul_of_nonneg_left (hcoarse (p.1,x+p.2) hp) (div_nonneg hk0 hell.le)).trans_eq (by ring)
  have hh := integral_mono_ae hi (href.1.const_mul (L/ell)) hle
  rw [integral_const_mul] at hh
  exact hh.trans ((mul_le_mul_of_nonneg_left href.2 (div_nonneg hL hell.le)).trans_eq (by ring))

theorem referenceConvolution_memLp (hages : ∀ i,σ i ≤ target i)
    {s τ ell L : ℝ} (hs : 0 < s) (hτ : -1 < τ) (hτ0 : τ ≤ 0)
    (hell : 0 < ell) (hL : 0 ≤ L) (hstop : ∀ i,s ≤ σ i)
    (e : Domain → ℝ) (he : Measurable e)
    (hcoarse : ∀ p,0 ≤ p.1 → |e p| ≤ L*p.1^τ) :
    MemLp (referenceConvolution σ target center hages ell e) 2 haarAddCircle := by
  apply bounded_memLp (referenceConvolution_measurable σ target center hages ell e he)
  intro x
  rw [abs_of_nonneg (referenceConvolution_nonneg σ target center hages hell e x)]
  exact referenceConvolution_bound σ target center hages hs hτ hτ0 hell hL hstop e he hcoarse x

theorem scoreInput_nonneg (hσ : ∀ i,0 < σ i) (hσ1 : ∀ i,σ i ≤ 1)
    (hages : ∀ i,σ i ≤ target i) (c : Domain → ℝ) (hc : Measurable c) (M ell : ℝ)
    (hcb : ∀ p,0 ≤ c p ∧ c p ≤ M) (hell : 0 < ell) (hcl : ∀ p,ell ≤ c p)
    (e : Domain → ℝ) (x : HeatCircle) : 0 ≤ scoreInput σ target center c e x := by
  let center' : Fin n → HeatCircle := fun i => center i+x
  have hr := row_mem_covariance_range_ae σ target center' hσ hσ1 hages c hc M ell hcb hell hcl
  have hA : (StoppedGaussianFeatures.stoppedCovariance σ target center' c 0).PosSemidef := by
    rw [← weightedFeature_gram σ target center' c hc M hcb hages 0]
    exact Matrix.posSemidef_gram ℝ _
  apply integral_nonneg_of_ae
  filter_upwards [hr] with p hp
  exact mul_nonneg (abs_nonneg _) (scoreVariance_nonneg hA hp)

/-- Sharp one-L² transfer for the actual full stopped canonical score
input, including physical output translations and singular covariance
ranks. Only joint scalar input data are used; no Lp-valued section map
or spatial independence premise is assumed. -/
theorem scoreInput_normTwo_bound (hσ : ∀ i,0 < σ i) (hσ1 : ∀ i,σ i ≤ 1)
    (hages : ∀ i,σ i ≤ target i) {s α τ ell K L : ℝ} (hs : 0 < s)
    (hα : -1 < α) (hα0 : α ≤ 0) (hτ : -1 < τ) (hτ0 : τ < 0)
    (hell : 0 < ell) (hK : 0 ≤ K) (hL : 0 ≤ L) (hstop : ∀ i,s ≤ σ i)
    (c : Domain → ℝ) (hc : Measurable c) (M : ℝ) (hcb : ∀ p,0 ≤ c p ∧ c p ≤ M)
    (hcl : ∀ p,ell ≤ c p) (e : Domain → ℝ) (he : Measurable e)
    (hcoarse : ∀ p,0 ≤ p.1 → |e p| ≤ L*p.1^τ)
    (hsharp : ∀ᵐ u ∂volume.restrict (Ici (0:ℝ)),normTwo haarAddCircle (fun z => e (u,z)) ≤ K*u^α)
    (hscore : Measurable (scoreInput σ target center c e)) :
    normTwo haarAddCircle (scoreInput σ target center c e) ≤
      K*(((n:ℝ)/ell)*(s/2)^α*(1+2/(α+1))) := by
  have hmem : MemLp (scoreInput σ target center c e) 2 haarAddCircle := by
    apply bounded_memLp hscore
    intro x
    rw [abs_of_nonneg (scoreInput_nonneg σ target center hσ hσ1 hages c hc M ell hcb hell hcl e x)]
    have hh := (score_input_weighted_bound σ target (fun i => center i+x) hσ hσ1 hages hs hτ hτ0
      hL hstop c hc M ell hcb hell hcl e he hcoarse).2
    exact hh
  have href := referenceConvolution_memLp σ target center hages hs hτ hτ0.le hell hL hstop e he hcoarse
  have hmono := normTwo_mono hmem href (ae_of_all _ (fun x => by
    rw [abs_of_nonneg (scoreInput_nonneg σ target center hσ hσ1 hages c hc M ell hcb hell hcl e x),
      abs_of_nonneg (referenceConvolution_nonneg σ target center hages hell e x)]
    exact score_integral_le_reference σ target center hσ hσ1 hages hs hτ hτ0.le hell hstop
      c hc M hcb hcl e he hcoarse x))
  apply hmono.trans
  exact referenceKernel_scalar_bound σ target center hages hs hα hα0 hτ hτ0.le hell hstop
    e he hK hL (by
      filter_upwards [ae_restrict_mem measurableSet_Ici] with u hu
      exact fun z => hcoarse (u,z) hu) hsharp

end SHE.StoppedScoreLeverage
