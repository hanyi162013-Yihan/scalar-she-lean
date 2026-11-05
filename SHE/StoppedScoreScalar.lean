module

public import SHE.StoppedScoreLeverage
public import SHE.ProfileL2

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section

namespace SHE.StoppedScoreLeverage
open Set MeasureTheory AddCircle Finset StoppedFourier StoppedGaussianFeatures GaussianAudit ProfileL2
open scoped InnerProductSpace
local instance stoppedScoreScalar_periodPos : Fact (0 < 2*Real.pi) := ⟨by positivity⟩
variable {n : ℕ} (σ target : Fin n → ℝ) (center : Fin n → HeatCircle)

theorem normTwo_abs_add (f : HeatCircle → ℝ) (y : HeatCircle) :
    normTwo haarAddCircle (fun x => |f (x+y)|) = normTwo haarAddCircle f := by
  unfold normTwo
  simp_rw [sq_abs]
  exact congrArg Real.sqrt (integral_add_right_eq_self (μ := haarAddCircle)
    (fun x : HeatCircle => f x^2) y)

theorem referenceKernel_power_mass (hages : ∀ i,σ i ≤ target i) {s α : ℝ}
    (hs : 0 < s) (hα : -1 < α) (hα0 : α ≤ 0) (hstop : ∀ i,s ≤ σ i) :
    Integrable (fun p => p.1^α*referenceKernel σ target center hages 0 p) (historyMeasure 0) ∧
      (∫ p,p.1^α*referenceKernel σ target center hages 0 p ∂historyMeasure 0) ≤
        (n:ℝ)*(s/2)^α*(1+2/(α+1)) := by
  rcases hα0.eq_or_lt with rfl | hα0
  · obtain ⟨hm,h0,hi,hmarg⟩ := physicalLeverage_properties
      (referenceCoefficients σ target center hages 0) σ target center hages
    obtain ⟨hp,hpeq⟩ := weighted_kernel_mass (volume.restrict (Ici 0))
      (referenceKernel σ target center hages 0) hm h0 hi (fun _ => 1) measurable_const
      (ae_of_all _ (fun _ => zero_le_one))
      (historyLeverage (referenceCoefficients σ target center hages 0) σ target center) hmarg
      (by simpa only [one_mul] using (historyLeverage_integrable
        (referenceCoefficients σ target center hages 0) σ target center hages 0))
    have hb : (∫ p,referenceKernel σ target center hages 0 p ∂historyMeasure 0) ≤ (n:ℝ) := by
      have heSum := integral_historyLeverage_energy
        (referenceCoefficients σ target center hages 0) σ target center hages 0
      have hmbound := heSum.le.trans (reference_history_energy_le σ target center hages)
      simpa only [one_mul] using! hpeq.le.trans (by simpa only [one_mul] using hmbound)
    refine ⟨by simpa only [Real.rpow_zero,one_mul] using! hp,?_⟩
    simpa only [Real.rpow_zero,one_mul,mul_one,zero_add,div_one] using hb.trans
      (by nlinarith [Nat.cast_nonneg (α := ℝ) n] : (n:ℝ) ≤ (n:ℝ)*(1+2))
  · exact referenceKernel_weighted_mass σ target center hages hs hα hα0 hstop

/-- A genuine scalar L² convolution estimate for the deterministic
canonical-score kernel. Joint scalar measurability is enough. A coarser
pointwise time power proves integrability, while only the sharper L²
time power enters the resulting bound. -/
theorem referenceKernel_scalar_bound (hages : ∀ i,σ i ≤ target i)
    {s α τ ell K L : ℝ} (hs : 0 < s) (hα : -1 < α) (hα0 : α ≤ 0)
    (hτ : -1 < τ) (hτ0 : τ ≤ 0) (hell : 0 < ell) (hstop : ∀ i,s ≤ σ i)
    (e : Domain → ℝ) (he : Measurable e) (hK : 0 ≤ K) (hL : 0 ≤ L)
    (hcoarse : ∀ᵐ u ∂volume.restrict (Ici (0:ℝ)),∀ z,|e (u,z)| ≤ L*u^τ)
    (hsharp : ∀ᵐ u ∂volume.restrict (Ici (0:ℝ)),
      normTwo haarAddCircle (fun z => e (u,z)) ≤ K*u^α) :
    normTwo haarAddCircle (fun x : HeatCircle => ∫ p : Domain,
      (referenceKernel σ target center hages 0 p/ell)*|e (p.1,x+p.2)| ∂historyMeasure 0) ≤
      K*(((n:ℝ)/ell)*(s/2)^α*(1+2/(α+1))) := by
  let k : Domain → ℝ := fun p => referenceKernel σ target center hages 0 p/ell
  obtain ⟨hkm,hk0,hki,hkmarg⟩ := physicalLeverage_properties
    (referenceCoefficients σ target center hages 0) σ target center hages
  have hm : Measurable k := hkm.div_const ell
  have h0 (p : Domain) : 0 ≤ k p := div_nonneg (hk0 p) hell.le
  have mass (γ : ℝ) (hγ : -1 < γ) (hγ0 : γ ≤ 0) :
      Integrable (fun p : Domain => k p*p.1^γ) (historyMeasure 0) ∧
      (∫ p : Domain,k p*p.1^γ ∂historyMeasure 0) ≤
        ((n:ℝ)/ell)*(s/2)^γ*(1+2/(γ+1)) := by
    have hh := referenceKernel_power_mass σ target center hages hs hγ hγ0 hstop
    refine ⟨by simpa only [k,div_eq_mul_inv,mul_comm,mul_left_comm,mul_assoc] using hh.1.div_const ell,?_⟩
    have heq : (fun p : Domain => k p*p.1^γ) = fun p => (p.1^γ*referenceKernel σ target center hages 0 p)*ell⁻¹ := by
      funext p
      dsimp only [k]
      ring
    rw [heq,integral_mul_const]
    exact (mul_le_mul_of_nonneg_right hh.2 (inv_nonneg.mpr hell.le)).trans_eq (by ring)
  let F : Domain × HeatCircle → ℝ := fun p => k p.1*|e (p.1.1,p.2+p.1.2)|
  let a : Domain → ℝ := fun p => K*(k p*p.1^α)
  let b : Domain → ℝ := fun p => L*(k p*p.1^τ)
  have hF : Measurable F := (hm.comp measurable_fst).mul
    ((continuous_abs.measurable.comp he).comp
      (measurable_fst.fst.prodMk (measurable_snd.add measurable_fst.snd)))
  have ha : Integrable a (historyMeasure 0) := (mass α hα hα0).1.const_mul K
  have hb : Integrable b (historyMeasure 0) := (mass τ hτ hτ0).1.const_mul L
  have ht0 : ∀ᵐ p : Domain ∂historyMeasure 0,0 ≤ p.1 := by
    exact Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem measurableSet_Ici)
  have ha0 : 0 ≤ᵐ[historyMeasure 0] a := ht0.mono (fun p hp =>
    mul_nonneg hK (mul_nonneg (h0 p) (Real.rpow_nonneg hp α)))
  have hb0 : 0 ≤ᵐ[historyMeasure 0] b := ht0.mono (fun p hp =>
    mul_nonneg hL (mul_nonneg (h0 p) (Real.rpow_nonneg hp τ)))
  have hFb : ∀ᵐ p ∂historyMeasure 0,∀ x,|F (p,x)| ≤ b p := by
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae hcoarse] with p hp
    intro x
    have hbound := mul_le_mul_of_nonneg_left (hp (x+p.2)) (h0 p)
    simpa only [F,b,abs_mul,abs_of_nonneg (h0 p),abs_abs,mul_assoc,mul_left_comm,mul_comm] using hbound
  have hFa : ∀ᵐ p ∂historyMeasure 0,normTwo haarAddCircle (fun x => F (p,x)) ≤ a p := by
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae hcoarse,
      Measure.quasiMeasurePreserving_fst.ae hsharp] with p hp hs'
    have heSection : MemLp (fun x : HeatCircle => |e (p.1,x+p.2)|) 2 haarAddCircle :=
      bounded_memLp ((continuous_abs.measurable.comp he).comp
        (measurable_const.prodMk (measurable_id.add measurable_const))) (fun x => by simpa only [abs_abs] using hp (x+p.2))
    change normTwo haarAddCircle (fun x => k p*|e (p.1,x+p.2)|) ≤ _
    rw [normTwo_const_mul heSection (k p),abs_of_nonneg (h0 p)]
    have htranslate := normTwo_abs_add (fun z => e (p.1,z)) p.2
    exact (congrArg (fun r : ℝ => k p*r) htranslate).le.trans
      ((mul_le_mul_of_nonneg_left hs' (h0 p)).trans_eq (by dsimp only [a]; ring))
  have hh := bounded_minkowski_two hF ha hb ha0 hb0 hFb hFa
  refine hh.trans ?_
  rw [show (∫ p,a p ∂historyMeasure 0) = K*(∫ p,k p*p.1^α ∂historyMeasure 0) from integral_const_mul K _]
  exact mul_le_mul_of_nonneg_left (mass α hα hα0).2 hK

end SHE.StoppedScoreLeverage
