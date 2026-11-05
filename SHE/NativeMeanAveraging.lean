module

public import SHE.NativeMeanFields

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
noncomputable section

/-! Genuine one-input Fubini averaging of canonical native mean-score energy
under arbitrary relative-center and predictable-profile dependence. -/
namespace SHE.NativeMeanAveraging
open Set MeasureTheory AddCircle Real StoppedFourier StoppedGaussianFeatures
  StoppedGaussianScore HeatTorus GaussianGramScore GaussianIncrement StoppedMeanEnergy
  RealHeatCovarianceMean MeasurableGaussianScores NativeMeanFields AllAgeMeanEnergy
open scoped InnerProductSpace
local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
variable [MeasurableSpace HeatTorus.CircleL2] [BorelSpace HeatTorus.CircleL2]

/-- The parameter may include all relative heat-tree coordinates, old noise,
and the signed input. No independence between those data is assumed. -/
theorem native_mean_score_one_input (n:ℕ) (hn:0<n) :
    ∃ h C:ℝ,0<h ∧ h≤1 ∧ 0<C ∧
      ∀ {X:Type*} [MeasurableSpace X] (ν:Measure X) [SFinite ν]
      (target:Fin n→ℝ) (a:X→Fin n→UnitAddCircle) (_ha:∀ i,Measurable (fun y=>a y i))
      (u Λ:ℝ),0<Λ →
      ∀ (t:Fin n→ℝ) (_ht:∀ i,0<t i),(∀ i,t i≤h) →
      ∀ (hage:∀ i,target i-u=4*π^2*t i) (s:ℝ) (hs:0<s) (hmin:∀ i,u+s≤target i)
      (c:(X×UnitAddCircle)×Domain→ℝ) (_hc:Measurable c) (U ell:ℝ)
      (_hcb:∀ p r,0≤c (p,r) ∧ c (p,r)≤U),0<ell → (∀ p r,ell≤c (p,r)) →
      ∀ (d:X→HeatTorus.CircleL2),Measurable d → Integrable (fun y=>‖d y‖^2) ν →
      let act:∀ i,u<target i:=fun i=>by linarith[hmin i]
      Integrable (meanScoreEnergy target a u Λ t hage act c d) (ν.prod haarAddCircle) ∧
      (∫ p,meanScoreEnergy target a u Λ t hage act c d p ∂ν.prod haarAddCircle)≤
        (C/ell)*(sqrt s)⁻¹*(∫ y,‖d y‖^2 ∂ν) := by
  obtain ⟨h,C,hh,hh1,hC,he⟩:=native_point_mean_energy n hn
  refine ⟨h,C,hh,hh1,hC,?_⟩
  intro X _ ν _ target a ha u Λ hΛ t ht hth hage s hs hmin c hc U ell hcb hell hcl d hd hid
  let act:∀ i,u<target i:=fun i=>by linarith[hmin i]
  let f:=meanScoreEnergy target a u Λ t hage act c d
  let B:ℝ:=(C/ell)*(sqrt s)⁻¹
  have hB:0≤B:=by dsimp[B];positivity
  have hfm:Measurable f:=meanScoreEnergy_measurable target a ha u Λ t ht hage act c hc d hd
  have hfn (p:X×UnitAddCircle):0≤f p:=
    meanScoreEnergy_nonneg target a u Λ hΛ t hage act s hs hmin c hc U ell hcb hell hcl d p
  have hci (y:X):Measurable (fun p:UnitAddCircle×Domain=>c ((y,p.1),p.2)):=
    hc.comp ((measurable_const.prodMk measurable_fst).prodMk measurable_snd)
  have hfib (y:X):Integrable (fun x=>f (y,x)) haarAddCircle ∧
      (∫ x,f (y,x) ∂haarAddCircle)≤B*‖d y‖^2:=by
    have hi:=he target (a y) u Λ hΛ t ht hth hage s hs (fun i=>by linarith[hmin i])
      (fun p=>c ((y,p.1),p.2)) (hci y) U ell (fun x r=>hcb (y,x) r) hell (fun x r=>hcl (y,x) r) (d y)
    exact hi
  have hinner:Integrable (fun y=>∫ x,f (y,x) ∂haarAddCircle) ν:=by
    apply (hid.const_mul B).mono' hfm.stronglyMeasurable.integral_prod_right'.aestronglyMeasurable
    apply ae_of_all
    intro y
    rw[Real.norm_of_nonneg (integral_nonneg (fun x=>hfn (y,x)))]
    exact (hfib y).2
  have hnorm:Integrable (fun y=>∫ x,‖f (y,x)‖ ∂haarAddCircle) ν:=by
    convert! hinner using 1
    funext y
    apply integral_congr_ae
    exact ae_of_all _ (fun x=>Real.norm_of_nonneg (hfn (y,x)))
  have hi:Integrable f (ν.prod haarAddCircle):=(integrable_prod_iff hfm.aestronglyMeasurable).mpr
    ⟨ae_of_all _ (fun y=>(hfib y).1),hnorm⟩
  refine ⟨hi,?_⟩
  rw[integral_prod _ hi]
  calc
    _≤∫ y,B*‖d y‖^2 ∂ν:=integral_mono hinner (hid.const_mul B) (fun y=>(hfib y).2)
    _=_:=integral_const_mul _ _

end SHE.NativeMeanAveraging
