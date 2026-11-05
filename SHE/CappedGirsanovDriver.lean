module
public import SHE.StandardTerminalGirsanov
public import SHE.CappedControlMeasureComparison
public import SHE.CylindricalDriverLaw
public import SHE.FiniteNoiseEuler
public import SHE.RotatedCylindricalBrownian
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1800000
namespace SHE.CappedGirsanovDriver
open MeasureTheory PredictableL2 StoppedItoInputs PredictableEnergyCap
open scoped NNReal ENNReal
variable {Ω C ι : Type*} [MeasurableSpace Ω]
variable [NormedAddCommGroup C] [InnerProductSpace ℝ C]
variable [MeasurableSpace C] [BorelSpace C] [SecondCountableTopology C] [DecidableEq ι]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ]
variable (H : ℝ≥0) (J : StandardTerminalIto (C:=C) (E:=ℝ) 𝓕 μ H)

/-- The drift-shifted coordinate is genuinely measurable on the original
space. No stochastic law or new version is used for this fact. -/
theorem shift_measurable (u R : Process (E:=C) 𝓕 μ H)
    (X : ℝ≥0→Ω→ℝ) (hX : ∀t,Measurable (X t)) (t : ℝ≥0) :
    Measurable (girsanovShift u R X t) := by
  have hR := (Lp.stronglyMeasurable R).mono (predictable_le_product 𝓕)
  have hu := (Lp.stronglyMeasurable u).mono (predictable_le_product 𝓕)
  have hm : StronglyMeasurable (fun p:ℝ≥0×Ω=>inner ℝ (R p) (u p)) :=
    continuous_inner.comp_stronglyMeasurable (hR.prodMk hu)
  exact (hX t).add hm.integral_prod_left.measurable

variable (U : ℝ≥0→Ω→C) (ha : StronglyAdapted 𝓕 U)
variable (hc : ∀ω,Continuous (fun t=>U t ω))
variable [Countable ι] (e : ι→C) (he : Orthonormal ℝ e)

def identityRowsMeasurable :
    @Measurable ((ℝ≥0×Ω)×C) C (𝓕.predictable.prod ‹MeasurableSpace C›) _
      (fun p=>(LinearIsometry.id : C→ₗᵢ[ℝ] C) p.2) := measurable_snd

def originalRow(i:ι):Process (E:=C) 𝓕 μ H:=
  RotatedCylindricalCoordinates.row 𝓕 μ H
    (fun _=>(LinearIsometry.id : C→ₗᵢ[ℝ] C)) (identityRowsMeasurable 𝓕) (e i)

def originalCoordinate(i:ι)(t:ℝ≥0)(ω:Ω):ℝ:=
  RotatedCylindricalCoordinates.coordinate 𝓕 μ H
    (fun _=>(LinearIsometry.id : C→ₗᵢ[ℝ] C)) (identityRowsMeasurable 𝓕) e J i t ω
local notation "R"=>originalRow 𝓕 μ H e
local notation "X"=>originalCoordinate 𝓕 μ H J e

include ha hc he in
/-- The actual capped control gives an equivalent probability on which
its literal shifted original coordinates have the common cylindrical
Brownian law. Expected cost, exit probability and all bounded-test
comparison bounds use the ORIGINAL uncapped control energy. -/
theorem exists_changed_driver (hNovikov : StandardTerminalNovikov J)
    (hGirsanov : StandardTerminalGirsanov J)
    (hH:(H:ℝ)≤1)(hH0:0<H)
    (hnull:NullCompleteFiltration.ContainsNullSets 𝓕 μ)
    (Bbdg:ℝ≥0)(hBDG:StandardTerminalBDG16 J Bbdg)
    (hi : Integrable (fun p:ℝ≥0×Ω=>‖U p.1 p.2‖^2) (energyMeasure μ H)) :
    ∃u:Process (E:=C) 𝓕 μ H,
      u=ᵐ[energyMeasure μ H] Function.uncurry (capped U) ∧
      (∀ᵐω∂μ,StochasticExponential.bracket 𝓕 μ H u ω≤1) ∧
      let Q:=ExponentialChangeMeasure.measure μ (fun ω=>J.integral u ω)
        (StochasticExponential.bracket 𝓕 μ H u)
      let cost:=∫p,‖U p.1 p.2‖^2 ∂energyMeasure μ H
      IsProbabilityMeasure Q ∧ μ≪Q ∧ Q≪μ ∧
      CylindricalDriverLaw.Law Q H (fun i=>girsanovShift u (R i) (X i)) ∧
      (∀i t,Measurable (girsanovShift u (R i) (X i) t)) ∧
      (∃K:StandardTerminalIto (C:=C) (E:=ℝ) 𝓕 Q H,
        ∀(f:Process (E:=C) 𝓕 μ H)(g:Process (E:=C) 𝓕 Q H),
          (∀ᵐp∂energyMeasure μ H,f p=g p)→
          (∀ᵐω∂Q,K.integral g ω=J.integral f ω+
            ∫s,inner ℝ (f (s,ω)) (u (s,ω)) ∂timeMeasure H)) ∧
      μ.real {ω|1≤accumulated U H ω}≤cost ∧
      (∀(f:Ω→ℝ)(B:ℝ),AEStronglyMeasurable f μ→0≤B→(∀ω,|f ω|≤B)→
        |(∫ω,f ω ∂Q)-(∫ω,f ω ∂μ)|≤2*B*Real.sqrt cost) ∧
      (∀(f g:Ω→ℝ)(B:ℝ),AEStronglyMeasurable f μ→AEStronglyMeasurable g μ→
        0≤B→(∀ω,|f ω|≤B)→(∀ω,|g ω|≤B)→
        (∀ω,ω∉{ω|1≤accumulated U H ω}→f ω=g ω)→
        |(∫ω,f ω ∂μ)-(∫ω,g ω ∂Q)|≤2*B*(Real.sqrt cost+cost)) := by
  obtain ⟨u,hu,hcap,hcost⟩ :=
    PredictableEnergyCapInput.exists_input 𝓕 μ H U ha hc hi
  have hmean:=StochasticExponential.mean_one_of_cap 𝓕 μ H J hNovikov u hcap
  have hQprob:=ExponentialChangeMeasure.probability μ (fun ω=>J.integral u ω)
    (StochasticExponential.bracket 𝓕 μ H u) hmean.1 hmean.2
  have hμQ:=ExponentialChangeMeasure.original_absolutelyContinuous μ (fun ω=>J.integral u ω)
    (StochasticExponential.bracket 𝓕 μ H u) hmean.1
  have hQμ:=ExponentialChangeMeasure.changed_absolutelyContinuous μ (fun ω=>J.integral u ω)
    (StochasticExponential.bracket 𝓕 μ H u)
  obtain ⟨hB,hBcost⟩:=PredictableEnergyCapInput.exit_bound 𝓕 μ H U ha hc hi
  have hent:=StochasticExponential.entropy 𝓕 μ H J u
  have hcost0:0≤∫p,‖U p.1 p.2‖^2 ∂energyMeasure μ H:=integral_nonneg (fun _=>sq_nonneg _)
  have hEntropy:-(∫ω,Real.log (StochasticExponential.density 𝓕 μ H J u ω) ∂μ)≤
      (∫p,‖U p.1 p.2‖^2 ∂energyMeasure μ H)/2:=by
    rw [hent.2]
    exact div_le_div_of_nonneg_right hcost (by norm_num)
  refine ⟨u,hu,hcap,hQprob,hμQ,hQμ,?_,?_,hGirsanov.transport u hcap,hBcost,?_,?_⟩
  · intro n a t ht
    apply (hGirsanov.finiteLaw u hcap n (fun i=>R (a i)) (fun i=>X (a i))
      (fun i j=>if a i=a j then 1 else 0) ?_ ?_ ?_ ?_).1 t ht
    · intro i
      exact RotatedCylindricalCoordinates.predictable_coordinate 𝓕 μ H
        (fun _=>(LinearIsometry.id : C→ₗᵢ[ℝ] C)) (identityRowsMeasurable 𝓕)
        e he J hH hH0 hnull Bbdg hBDG (a i)
    · intro i ω
      exact RotatedCylindricalCoordinates.continuous_coordinate 𝓕 μ H
        (fun _=>(LinearIsometry.id : C→ₗᵢ[ℝ] C)) (identityRowsMeasurable 𝓕)
        e he J hH0 (a i) ω
    · intro s hs
      filter_upwards [RotatedCylindricalCoordinates.coordinate_ae 𝓕 μ H
        (fun _=>(LinearIsometry.id : C→ₗᵢ[ℝ] C)) (identityRowsMeasurable 𝓕)
        e he J hH hH0 Bbdg hBDG s] with ω hω i
      have hsr:(s:ℝ)≤(H:ℝ):=by exact_mod_cast hs
      simpa only [originalCoordinate,originalRow,min_eq_left hs,min_eq_left hsr] using hω (a i)
    · filter_upwards [RotatedCylindricalCoordinates.all_gram 𝓕 μ H
        (fun _=>(LinearIsometry.id : C→ₗᵢ[ℝ] C)) (identityRowsMeasurable 𝓕)
        e he] with p hp i j
      exact hp (a i) (a j)
  · intro i t
    exact shift_measurable 𝓕 μ H u (R i) (X i)
      (fun s=>RotatedCylindricalBrownian.coordinate_measurable 𝓕 μ H
        (fun _=>(LinearIsometry.id : C→ₗᵢ[ℝ] C)) (identityRowsMeasurable 𝓕)
        e he J hH hH0 hnull Bbdg hBDG i s) t
  · intro f B hf hB0 hbf
    exact SHE.density_test_bound μ (fun _=>Real.exp_pos _) hmean.1 hmean.2
      hent.1 hcost0 hEntropy hf hB0 hbf
  · intro f g B hf hg hB0 hbf hbg hagree
    exact SHE.stopped_measure_comparison μ (fun _=>Real.exp_pos _) hmean.1 hmean.2
      hent.1 hcost0 hEntropy hB hBcost hf hg hB0 hbf hbg hagree
end SHE.CappedGirsanovDriver
