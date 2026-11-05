module

public import SHE.NativeMeanAveraging
public import SHE.GaussianScoreKernel

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
noncomputable section

/-! Actual dependent native Gaussian score energy: the covariance varies
with every relative-center/profile parameter, and its own Gaussian kernel
is integrated together with the sole signed input. -/
namespace SHE.NativeMeanScoreKernel
open Set MeasureTheory ProbabilityTheory AddCircle Real StoppedFourier StoppedGaussianFeatures
  StoppedGaussianScore StoppedCanonicalScore HeatHistoryScore HeatTorus HeatTorusKernel
  GaussianGramScore GaussianIncrement StoppedMeanEnergy RealHeatCovarianceMean
  MeasurableGaussianScores HeatChristoffelTransfer NativeMeanFields NativeMeanAveraging
  GaussianScoreKernel MeasurableGeneralizedInverse
open scoped InnerProductSpace
local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
variable {X:Type*} [MeasurableSpace X] {n:ℕ}
variable [MeasurableSpace HeatTorus.CircleL2] [BorelSpace HeatTorus.CircleL2]

def covarianceField (target:Fin n→ℝ) (a:X→Fin n→UnitAddCircle)
    (c:(X×UnitAddCircle)×Domain→ℝ) (u:ℝ) (p:X×UnitAddCircle) : Mat n :=
  StoppedGaussianFeatures.stoppedCovariance target target (nativeCenter (fun i=>a p.1 i+p.2))
    (fun r=>c (p,r)) u

def directionField (target:Fin n→ℝ) (a:X→Fin n→UnitAddCircle) (u Λ:ℝ)
    (t:Fin n→ℝ) (hage:∀i,target i-u=4*π^2*t i) (hact:∀i,u<target i)
    (d:X→HeatTorus.CircleL2) (p:X×UnitAddCircle) : State n :=
  meanDirection (dampedSynthesis target target (fun i=>a p.1 i+p.2) u Λ t hage hact) (d p.1)

omit [MeasurableSpace HeatTorus.CircleL2] [BorelSpace HeatTorus.CircleL2] in
theorem covarianceField_measurable (target:Fin n→ℝ) (a:X→Fin n→UnitAddCircle)
    (ha:∀i,Measurable (fun y=>a y i)) (c:(X×UnitAddCircle)×Domain→ℝ) (hc:Measurable c) (u:ℝ) :
    Measurable (covarianceField target a c u) :=
  StoppedGaussianFields.covariance_measurable (NativeMeanFields.observations target a ha) hc measurable_const

theorem directionField_measurable (target:Fin n→ℝ) (a:X→Fin n→UnitAddCircle)
    (ha:∀i,Measurable (fun y=>a y i)) (u Λ:ℝ) (t:Fin n→ℝ) (ht:∀i,0<t i)
    (hage:∀i,target i-u=4*π^2*t i) (hact:∀i,u<target i)
    (d:X→HeatTorus.CircleL2) (hd:Measurable d) :
    Measurable (directionField target a u Λ t hage hact d) := by
  have hS (i:Fin n):StronglyMeasurable (fun p:X×UnitAddCircle=>
      dampedSynthesis target target (fun j=>a p.1 j+p.2) u Λ t hage hact
        (EuclideanSpace.basisFun (Fin n) ℝ i)):=by
    have hcenter:Measurable (fun p:X×UnitAddCircle=>a p.1 i+p.2):=
      ((ha i).comp measurable_fst).add measurable_snd
    have hm:=continuous_translate_action.measurable.comp
      (hcenter.prodMk (measurable_const (a:=unitHeatKernel (t i) (0:UnitAddCircle))))
    convert! hm.stronglyMeasurable.const_smul (exp (-Λ*(target i-u)):ℂ) using 1
    funext p
    rw[dampedSynthesis_basis]
    change (exp (-Λ*(target i-u)):ℂ) • unitHeatKernel (t i) (a p.1 i+p.2)=
      (exp (-Λ*(target i-u)):ℂ) • translate (a p.1 i+p.2) (unitHeatKernel (t i) 0)
    rw[translate_unitHeatKernel (ht i),zero_add]
  apply (WithLp.measurable_toLp 2 (Fin n→ℝ)).comp
  apply Measurable.of_eval
  intro i
  have hm:=((hS i).inner (𝕜:=ℂ) (hd.comp measurable_fst).stronglyMeasurable).measurable
  convert! Complex.continuous_re.measurable.comp hm using 1
  funext p
  exact meanDirection_apply _ _ i

omit [MeasurableSpace HeatTorus.CircleL2] [BorelSpace HeatTorus.CircleL2] in
theorem physical_mean_direction_mem_range (target:Fin n→ℝ) (a:Fin n→UnitAddCircle)
    (u Λ:ℝ) (hΛ:0<Λ) (t:Fin n→ℝ) (hage:∀i,target i-u=4*π^2*t i)
    (hact:∀i,u<target i) (s:ℝ) (hs:0<s) (hmin:∀i,u+s≤target i)
    (c:Domain→ℝ) (hc:Measurable c) (U ell:ℝ) (hcb:∀r,0≤c r ∧ c r≤U)
    (hell:0<ell) (hcl:∀r,ell≤c r) (d:HeatTorus.CircleL2) :
    meanDirection (dampedSynthesis target target a u Λ t hage hact) d∈
      (Matrix.toEuclideanCLM (𝕜:=ℝ) (StoppedGaussianFeatures.stoppedCovariance target target (nativeCenter a) c u)).range := by
  let v:=weightedFeature target target (nativeCenter a) c hc U hcb (fun _=>le_rfl) u
  let S:=dampedSynthesis target target a u Λ t hage hact
  have hrow (z:State n):‖S z‖≤sqrt (2/(ell*s))*‖featureSynthesis v z‖:=by
    have hcE:=(weightedSynthesis_full_history_bounds target target (nativeCenter a) c hc U hcb
      (fun _=>le_rfl) hcl u z).1
    have hcurr:=stopped_damped_current_row_bound Finset.univ (fun i=>(z i:ℂ)) target target
      (nativeCenter a) (fun _ _=>le_rfl) hΛ hs (fun i _=>hmin i)
    have hSn:‖S z‖^2=‖historyG Finset.univ (fun i=>(z i:ℂ)) target target
      (nativeCenter a) Λ u‖^2:=realDamped_norm_sq _ _ _ _ _ _ _ _ z
    apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (sqrt_nonneg _) (norm_nonneg _))).mp
    rw[mul_pow,sq_sqrt (by positivity:0≤2/(ell*s)),hSn]
    have he:=mul_le_mul_of_nonneg_left hcE (show 0≤2/(ell*s) by positivity)
    have he':(2/s)*(fullPhysicalEnergy (historyF Finset.univ (fun i=>(z i:ℂ)) target target
      (nativeCenter a)) u).toReal≤(2/(ell*s))*‖featureSynthesis v z‖^2:=by
      convert! he using 1;field_simp
    exact hcurr.trans he'
  have hr:=(scoreVariance_projection_bound t a S v
    (fun z=>dampedSynthesis_span _ _ _ _ _ _ _ _ z) (sqrt_nonneg _) hrow d).1
  have he:=weightedFeature_gram target target (nativeCenter a) c hc U hcb (fun _=>le_rfl) u
  change Matrix.gram ℝ v=_ at he
  rw[he] at hr
  exact hr

/-- True dependent Gaussian square-score energy under the composition
product law, with a single signed L2 input. -/
theorem native_gaussian_mean_score_one_input (n:ℕ) (hn:0<n) :
    ∃ h C:ℝ,0<h ∧ h≤1 ∧ 0<C ∧
      ∀ {X:Type*} [MeasurableSpace X] (ν:Measure X) [SFinite ν]
      (target:Fin n→ℝ) (a:X→Fin n→UnitAddCircle) (ha:∀i,Measurable (fun y=>a y i))
      (u Λ:ℝ),0<Λ →
      ∀ (t:Fin n→ℝ) (ht:∀i,0<t i),(∀i,t i≤h) →
      ∀ (hage:∀i,target i-u=4*π^2*t i) (s:ℝ) (hs:0<s) (hmin:∀i,u+s≤target i)
      (c:(X×UnitAddCircle)×Domain→ℝ) (hc:Measurable c) (U ell:ℝ)
      (hcb:∀p r,0≤c (p,r) ∧ c (p,r)≤U),0<ell → (∀p r,ell≤c (p,r)) →
      ∀ (d:X→HeatTorus.CircleL2),Measurable d → Integrable (fun y=>‖d y‖^2) ν →
      let act:∀i,u<target i:=fun i=>by linarith[hmin i]
      let A:=covarianceField target a c u
      let D:=directionField target a u Λ t hage act d
      let κ:=gaussianKernel A (covarianceField_measurable target a ha c hc u)
      Integrable (fun p:(X×UnitAddCircle)×State n=>|firstScore (A p.1) (D p.1) p.2|^2)
        ((ν.prod haarAddCircle)⊗ₘκ) ∧
      (∫p:(X×UnitAddCircle)×State n,|firstScore (A p.1) (D p.1) p.2|^2 ∂(ν.prod haarAddCircle)⊗ₘκ)≤
        (C/ell)*(sqrt s)⁻¹*(∫y,‖d y‖^2 ∂ν) := by
  obtain ⟨h,C,hh,hh1,hC,he⟩:=native_mean_score_one_input n hn
  refine ⟨h,C,hh,hh1,hC,?_⟩
  intro X _ ν _ target a ha u Λ hΛ t ht hth hage s hs hmin c hc U ell hcb hell hcl d hd hid
  let act:∀i,u<target i:=fun i=>by linarith[hmin i]
  let A:=covarianceField target a c u
  let D:=directionField target a u Λ t hage act d
  have hAm:Measurable A:=covarianceField_measurable target a ha c hc u
  have hDm:Measurable D:=directionField_measurable target a ha u Λ t ht hage act d hd
  have hApos (p:X×UnitAddCircle):(A p).PosSemidef:=
    StoppedGaussianFields.covariance_posSemidef (NativeMeanFields.observations target a ha) c (fun _=>u) p
      (hc.comp (measurable_const.prodMk measurable_id)) (hcb p) (fun _=>le_rfl)
  have hDr (p:X×UnitAddCircle):D p∈(Matrix.toEuclideanCLM (𝕜:=ℝ) (A p)).range:=
    physical_mean_direction_mem_range target (fun i=>a p.1 i+p.2) u Λ hΛ t hage act s hs hmin
      (fun r=>c (p,r)) (hc.comp (measurable_const.prodMk measurable_id)) U ell (hcb p) hell (hcl p) (d p.1)
  have hmean:=he ν target a ha u Λ hΛ t ht hth hage s hs hmin c hc U ell hcb hell hcl d hd hid
  have hV:Integrable (fun p:X×UnitAddCircle=>scoreVariance (A p) (D p)^1) (ν.prod haarAddCircle):=by
    convert! hmean.1 using 1
    funext p
    simp only [pow_one,A,D,covarianceField,directionField,meanScoreEnergy]
  have hk:=firstScore_kernel_even_moments (ν.prod haarAddCircle) A hAm hApos D hDm hDr 1 hV
  simp only [show 2*1=2 by rfl,pow_one,firstScoreMoment_one,mul_one] at hk
  exact ⟨hk.1,hk.2.trans_le hmean.2⟩

end SHE.NativeMeanScoreKernel
