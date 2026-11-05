module

public import SHE.AllAgeMeanEnergy
public import SHE.HilbertColumns

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
noncomputable section

/-! Actual jointly measurable native mean-score energies for arbitrary
relative-center and coefficient-profile parameter fields. Dependence on the
parameter and on the signed L2 input is retained throughout. -/
namespace SHE.NativeMeanFields
open Set MeasureTheory AddCircle Real StoppedFourier StoppedGaussianFeatures
  StoppedGaussianScore StoppedCanonicalScore HeatHistoryScore HeatTorus HeatTorusKernel
  GaussianGramScore GaussianIncrement StoppedMeanEnergy RealHeatCovarianceMean
  MeasurableGaussianScores HeatChristoffelTransfer
open scoped InnerProductSpace
local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

variable {X : Type*} [MeasurableSpace X] {n : ℕ}

instance circle_secondCountable : SecondCountableTopology HeatTorus.CircleL2 := by
  let _ : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
  exact (_root_.fourierBasis (T := (1 : ℝ))).repr.toHomeomorph.secondCountableTopology

def observations (target : Fin n → ℝ) (a : X → Fin n → UnitAddCircle)
    (ha : ∀ i, Measurable (fun y=>a y i)) : VariableObservations.Family (X×UnitAddCircle) n where
  observations p i:=⟨target i,target i,nativeCenter (fun j=>a p.1 j+p.2) i⟩
  stop_measurable _:=measurable_const
  target_measurable _:=measurable_const
  center_measurable i:=(CircleNormalization.continuous_scale 1 (2*π)).measurable.comp
    (((ha i).comp measurable_fst).add measurable_snd)

def meanScoreEnergy (target : Fin n → ℝ) (a : X → Fin n → UnitAddCircle) (u Λ : ℝ)
    (t : Fin n → ℝ) (hage : ∀ i,target i-u=4*π^2*t i) (hact : ∀ i,u<target i)
    (c : (X×UnitAddCircle)×Domain → ℝ) (d : X → HeatTorus.CircleL2) (p : X×UnitAddCircle) : ℝ :=
  scoreVariance (StoppedGaussianFeatures.stoppedCovariance target target
    (nativeCenter (fun i=>a p.1 i+p.2)) (fun r=>c (p,r)) u)
    (meanDirection (dampedSynthesis target target (fun i=>a p.1 i+p.2) u Λ t hage hact) (d p.1))

theorem meanScoreEnergy_measurable [MeasurableSpace HeatTorus.CircleL2] [BorelSpace HeatTorus.CircleL2]
    (target : Fin n → ℝ) (a : X → Fin n → UnitAddCircle)
    (ha : ∀ i,Measurable (fun y=>a y i)) (u Λ : ℝ) (t : Fin n → ℝ) (ht : ∀ i,0<t i)
    (hage : ∀ i,target i-u=4*π^2*t i) (hact : ∀ i,u<target i)
    (c : (X×UnitAddCircle)×Domain → ℝ) (hc : Measurable c)
    (d : X → HeatTorus.CircleL2) (hd : Measurable d) :
    Measurable (meanScoreEnergy target a u Λ t hage hact c d) := by
  have hcov:=StoppedGaussianFields.covariance_measurable (observations target a ha) hc (measurable_const (a:=u))
  have hS (i:Fin n) : StronglyMeasurable (fun p:X×UnitAddCircle=>
      dampedSynthesis target target (fun j=>a p.1 j+p.2) u Λ t hage hact
        (EuclideanSpace.basisFun (Fin n) ℝ i)) := by
    have hcenter:Measurable (fun p:X×UnitAddCircle=>a p.1 i+p.2):=
      ((ha i).comp measurable_fst).add measurable_snd
    have hm:=continuous_translate_action.measurable.comp
      (hcenter.prodMk (measurable_const (a:=unitHeatKernel (t i) (0:UnitAddCircle))))
    have hs:=hm.stronglyMeasurable.const_smul (exp (-Λ*(target i-u)):ℂ)
    convert! hs using 1
    funext p
    rw[dampedSynthesis_basis]
    change (exp (-Λ*(target i-u)):ℂ) • unitHeatKernel (t i) (a p.1 i+p.2) =
      (exp (-Λ*(target i-u)):ℂ) • translate (a p.1 i+p.2) (unitHeatKernel (t i) 0)
    rw[translate_unitHeatKernel (ht i),zero_add]
  have hdir:Measurable (fun p:X×UnitAddCircle=>meanDirection
      (dampedSynthesis target target (fun i=>a p.1 i+p.2) u Λ t hage hact) (d p.1)):=by
    apply (WithLp.measurable_toLp 2 (Fin n→ℝ)).comp
    apply Measurable.of_eval
    intro i
    have hm:=((hS i).inner (𝕜:=ℂ) (hd.comp measurable_fst).stronglyMeasurable).measurable
    have hr:=Complex.continuous_re.measurable.comp hm
    convert! hr using 1
    funext p
    exact meanDirection_apply _ _ i
  convert! scoreVariance_measurable.comp (hcov.prodMk hdir) using 1

/-- Range membership and positivity are derived from the original physical
history. Positivity is not assumed for an off-range generalized inverse. -/
theorem meanScoreEnergy_nonneg (target : Fin n → ℝ) (a : X → Fin n → UnitAddCircle)
    (u Λ : ℝ) (hΛ:0<Λ) (t : Fin n → ℝ) (hage : ∀ i,target i-u=4*π^2*t i)
    (hact : ∀ i,u<target i) (s:ℝ) (hs:0<s) (hmin:∀ i,u+s≤target i)
    (c : (X×UnitAddCircle)×Domain → ℝ) (hc : Measurable c) (U ell:ℝ)
    (hcb:∀ p r,0≤c (p,r) ∧ c (p,r)≤U) (hell:0<ell) (hcl:∀ p r,ell≤c (p,r))
    (d : X → HeatTorus.CircleL2) (p:X×UnitAddCircle) :
    0≤meanScoreEnergy target a u Λ t hage hact c d p := by
  let v:=weightedFeature target target (nativeCenter (fun i=>a p.1 i+p.2)) (fun r=>c (p,r))
    (hc.comp (measurable_const.prodMk measurable_id)) U (hcb p) (fun _=>le_rfl) u
  let S:=dampedSynthesis target target (fun i=>a p.1 i+p.2) u Λ t hage hact
  have hrow (z:State n):‖S z‖≤sqrt (2/(ell*s))*‖featureSynthesis v z‖:=by
    have hcE:=(weightedSynthesis_full_history_bounds target target (nativeCenter (fun i=>a p.1 i+p.2))
      (fun r=>c (p,r)) (hc.comp (measurable_const.prodMk measurable_id)) U (hcb p) (fun _=>le_rfl)
      (hcl p) u z).1
    have hcurr:=stopped_damped_current_row_bound Finset.univ (fun i=>(z i:ℂ)) target target
      (nativeCenter (fun i=>a p.1 i+p.2)) (fun _ _=>le_rfl) hΛ hs (fun i _=>hmin i)
    have hSn:‖S z‖^2=‖historyG Finset.univ (fun i=>(z i:ℂ)) target target
      (nativeCenter (fun i=>a p.1 i+p.2)) Λ u‖^2:=realDamped_norm_sq _ _ _ _ _ _ _ _ z
    apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (sqrt_nonneg _) (norm_nonneg _))).mp
    rw[mul_pow,sq_sqrt (by positivity:0≤2/(ell*s)),hSn]
    have he:=mul_le_mul_of_nonneg_left hcE (show 0≤2/(ell*s) by positivity)
    have he':(2/s)*(fullPhysicalEnergy (historyF Finset.univ (fun i=>(z i:ℂ)) target target
      (nativeCenter (fun i=>a p.1 i+p.2))) u).toReal≤(2/(ell*s))*‖featureSynthesis v z‖^2:=by
      convert! he using 1;field_simp
    exact hcurr.trans he'
  have hr:=(scoreVariance_projection_bound t (fun i=>a p.1 i+p.2) S v
    (fun z=>dampedSynthesis_span _ _ _ _ _ _ _ _ z) (sqrt_nonneg _) hrow (d p.1)).1
  have hn:=scoreVariance_nonneg (Matrix.posSemidef_gram ℝ v) hr
  have he:=weightedFeature_gram target target (nativeCenter (fun i=>a p.1 i+p.2)) (fun r=>c (p,r))
    (hc.comp (measurable_const.prodMk measurable_id)) U (hcb p) (fun _=>le_rfl) u
  change Matrix.gram ℝ v=_ at he
  rw[he] at hn
  exact hn

end SHE.NativeMeanFields
