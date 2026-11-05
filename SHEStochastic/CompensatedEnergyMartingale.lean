module

public import SHEStochastic.WeakLimitUniformEnergy
public import SHEStochastic.BCFL1PastTesting

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
noncomputable section

namespace SHEStochastic.CompensatedEnergyMartingale
open MeasureTheory Filter
open scoped Topology ENNReal
variable {X Y T : Type*} [UniformSpace X] [TopologicalSpace.MetrizableSpace X]
    [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace Y] [TopologicalSpace.MetrizableSpace Y] [MeasurableSpace Y] [BorelSpace Y] [Preorder T]

def value (M A : T → X → ℝ) (t : T) (x : X) : ℝ := (M t x)^2-A t x

def productValue (M N A : T → X → ℝ) (t : T) (x : X) : ℝ := M t x*N t x-A t x

/-- Quadratic martingale characteristics survive compact-uniform
compensator convergence using only first energy moments and energy UI.
The coefficients may be unbounded and all source laws may differ. -/
theorem product (P : ℕ → ProbabilityMeasure X) (Q : ProbabilityMeasure X)
    (hP : Tendsto P atTop (𝓝 Q))
    (hTight : IsTightMeasureSet (Set.range (fun m => (P m).toMeasure)))
    (energy : X → ℝ) (he : Continuous energy) (hpos : ∀ x,0≤energy x)
    (hUI : Tendsto (fun R : ℕ => ⨆ m,∫⁻ x in {x | (R : ℝ)≤energy x},
      ENNReal.ofReal (energy x) ∂(P m).toMeasure) atTop (𝓝 0))
    (F : Filtration T (inferInstance : MeasurableSpace X)) (past : T → X → Y)
    (hpast : ∀ t,Continuous (past t)) (hF : ∀ t,F t≤MeasurableSpace.comap (past t) inferInstance)
    (M N A : T → X → ℝ) (An : ℕ → T → X → ℝ)
    (hcM : ∀ t,Continuous (M t)) (hcN : ∀ t,Continuous (N t)) (hcA : ∀ t,Continuous (A t)) (hcAn : ∀ m t,Continuous (An m t))
    (haM : StronglyAdapted F M) (haN : StronglyAdapted F N) (haA : StronglyAdapted F A)
    (hclose : ∀ t K,IsCompact K → TendstoUniformlyOn (fun m => An m t) (A t) atTop K)
    (K D : ℝ) (hK : 0≤K) (hD : 0≤D)
    (hM : ∀ t x,|M t x*N t x|≤K*(1+energy x))
    (hA : ∀ t x,|A t x|≤D*(1+energy x)) (hAn : ∀ m t x,|An m t x|≤D*(1+energy x))
    (htest : ∀ m s t,s≤t → ∀ ψ : BoundedContinuousFunction Y ℝ,
      (∫ x,ψ (past s x)*(productValue M N (An m) t x-productValue M N (An m) s x) ∂(P m).toMeasure)=0) :
    Martingale (productValue M N A) F Q.toMeasure := by
  have hvalue (B : T → X → ℝ) (hB : ∀ t x,|B t x|≤D*(1+energy x)) (t : T) (x : X) :
      |productValue M N B t x|≤(K+D)*(1+energy x) := by
    apply (abs_sub (M t x*N t x) (B t x)).trans
    exact (add_le_add (hM t x) (hB t x)).trans_eq (by ring)
  have hQi (t : T) : Integrable (productValue M N A t) Q.toMeasure := by
    have hlim (S : Set X) (hS : IsCompact S) :
        TendstoUniformlyOn (fun m => productValue M N (An m) t) (productValue M N A t) atTop S := by
      exact CompactUniformComposition.with_parameter hS (fun m => hcAn m t) (hcA t) (hclose t S hS)
        (fun z : X×ℝ => M t z.1*N t z.1-z.2) (((hcM t).comp continuous_fst).mul ((hcN t).comp continuous_fst) |>.sub continuous_snd)
    exact (WeakLimitUniformEnergy.integral_tendsto P Q hP hTight energy he hpos hUI
      (fun m => productValue M N (An m) t) (fun m => (hcM t).mul (hcN t) |>.sub (hcAn m t))
      (productValue M N A t) ((hcM t).mul (hcN t) |>.sub (hcA t)) hlim (K+D) (add_nonneg hK hD)
      (fun m => hvalue (An m) (hAn m) t) (hvalue A hA t)).2.1
  have ha : StronglyAdapted F (productValue M N A) := by
    intro t
    have ht := ((haM t).mul (haN t)).sub (haA t)
    change StronglyMeasurable[F t] (fun x => M t x*N t x-A t x) at ht
    change StronglyMeasurable[F t] (fun x => M t x*N t x-A t x)
    exact ht
  apply BCFL1PastTesting.martingale Q.toMeasure F past (fun t => (hpast t).measurable) hF
    (productValue M N A) ha hQi
  intro s t hst ψ
  have hgrowth (B : T → X → ℝ) (hB : ∀ t x,|B t x|≤D*(1+energy x)) (x : X) :
      |ψ (past s x)*(productValue M N B t x-productValue M N B s x)|≤(2*‖ψ‖*(K+D))*(1+energy x) := by
    rw [abs_mul]
    apply (mul_le_mul (ψ.norm_coe_le_norm (past s x)) (abs_sub _ _)
      (abs_nonneg _) (norm_nonneg _)).trans
    have hh := mul_le_mul_of_nonneg_left
      (add_le_add (hvalue B hB t x) (hvalue B hB s x)) (norm_nonneg ψ)
    exact hh.trans_eq (by ring)
  have hlim (S : Set X) (hS : IsCompact S) :
      TendstoUniformlyOn (fun m x => ψ (past s x)*(productValue M N (An m) t x-productValue M N (An m) s x))
        (fun x => ψ (past s x)*(productValue M N A t x-productValue M N A s x)) atTop S := by
    have hp : TendstoUniformlyOn (fun m x => (An m t x,An m s x)) (fun x => (A t x,A s x)) atTop S := by
      intro V hV
      exact (tendsto_id.prodMk tendsto_id) (((hclose t S hS).prodMk (hclose s S hS)) V hV)
    exact CompactUniformComposition.with_parameter hS (fun m => (hcAn m t).prodMk (hcAn m s))
      ((hcA t).prodMk (hcA s)) hp
      (fun z : X×(ℝ×ℝ) => ψ (past s z.1)*((M t z.1*N t z.1-z.2.1)-(M s z.1*N s z.1-z.2.2)))
      ((ψ.continuous.comp ((hpast s).comp continuous_fst)).mul
        ((((hcM t).comp continuous_fst).mul ((hcN t).comp continuous_fst) |>.sub continuous_snd.fst).sub
          (((hcM s).comp continuous_fst).mul ((hcN s).comp continuous_fst) |>.sub continuous_snd.snd)))
  have hc (B : T → X → ℝ) (hB : ∀ q,Continuous (B q)) :
      Continuous (fun x => ψ (past s x)*(productValue M N B t x-productValue M N B s x)) :=
    (ψ.continuous.comp (hpast s)).mul
      (((hcM t).mul (hcN t) |>.sub (hB t)).sub ((hcM s).mul (hcN s) |>.sub (hB s)))
  have ht := (WeakLimitUniformEnergy.integral_tendsto P Q hP hTight energy he hpos hUI
    (fun m x => ψ (past s x)*(productValue M N (An m) t x-productValue M N (An m) s x))
    (fun m => hc (An m) (hcAn m))
    (fun x => ψ (past s x)*(productValue M N A t x-productValue M N A s x)) (hc A hcA) hlim
    (2*‖ψ‖*(K+D)) (by positivity) (fun m => hgrowth (An m) (hAn m)) (hgrowth A hA)).2.2
  have hz : Tendsto (fun m => ∫ x,ψ (past s x)*(productValue M N (An m) t x-productValue M N (An m) s x) ∂(P m).toMeasure)
      atTop (𝓝 0) := tendsto_const_nhds.congr (fun m => (htest m s t hst ψ).symm)
  exact tendsto_nhds_unique ht hz


/-- The square-characteristic interface is retained as a specialization
of the product closure, so the same proof handles mixed characteristics. -/
theorem martingale (P : ℕ → ProbabilityMeasure X) (Q : ProbabilityMeasure X)
    (hP : Tendsto P atTop (𝓝 Q))
    (hTight : IsTightMeasureSet (Set.range (fun m => (P m).toMeasure)))
    (energy : X → ℝ) (he : Continuous energy) (hpos : ∀ x,0≤energy x)
    (hUI : Tendsto (fun R : ℕ => ⨆ m,∫⁻ x in {x | (R : ℝ)≤energy x},
      ENNReal.ofReal (energy x) ∂(P m).toMeasure) atTop (𝓝 0))
    (F : Filtration T (inferInstance : MeasurableSpace X)) (past : T → X → Y)
    (hpast : ∀ t,Continuous (past t)) (hF : ∀ t,F t≤MeasurableSpace.comap (past t) inferInstance)
    (M A : T → X → ℝ) (An : ℕ → T → X → ℝ)
    (hcM : ∀ t,Continuous (M t)) (hcA : ∀ t,Continuous (A t)) (hcAn : ∀ m t,Continuous (An m t))
    (haM : StronglyAdapted F M) (haA : StronglyAdapted F A)
    (hclose : ∀ t K,IsCompact K → TendstoUniformlyOn (fun m => An m t) (A t) atTop K)
    (K D : ℝ) (hK : 0≤K) (hD : 0≤D)
    (hM : ∀ t x,(M t x)^2≤K*(1+energy x))
    (hA : ∀ t x,|A t x|≤D*(1+energy x)) (hAn : ∀ m t x,|An m t x|≤D*(1+energy x))
    (htest : ∀ m s t,s≤t → ∀ ψ : BoundedContinuousFunction Y ℝ,
      (∫ x,ψ (past s x)*(value M (An m) t x-value M (An m) s x) ∂(P m).toMeasure)=0) :
    Martingale (value M A) F Q.toMeasure := by
  have hprod : ∀ t x,|M t x*M t x|≤K*(1+energy x) := by
    intro t x
    rw [←pow_two,abs_of_nonneg (sq_nonneg _)]
    exact hM t x
  have ht := product P Q hP hTight energy he hpos hUI F past hpast hF M M A An
    hcM hcM hcA hcAn haM haM haA hclose K D hK hD hprod hA hAn
    (fun m s t hst ψ => by
      simpa only [productValue,value,pow_two] using htest m s t hst ψ)
  have hv : value M A=productValue M M A := by
    funext t x
    dsimp only [value,productValue]
    rw [pow_two]
  rw [hv]
  exact ht

end SHEStochastic.CompensatedEnergyMartingale
