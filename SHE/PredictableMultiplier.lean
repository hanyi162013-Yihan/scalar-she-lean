module
public import SHE.PredictableContraction
public import SHE.PredictableClock
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace SHE.PredictableMultiplier
open MeasureTheory PredictableL2
open scoped NNReal ENNReal
variable {Ω E:Type*}[MeasurableSpace Ω][NormedAddCommGroup E][NormedSpace ℝ E]
variable (𝓕:Filtration ℝ≥0 ‹MeasurableSpace Ω›)(μ:Measure Ω)(h:ℝ≥0)
variable (a:ℝ≥0×Ω→ℝ)(ha:StronglyMeasurable[𝓕.predictable] a)(B:ℝ)(hb:∀p,|a p|≤B)

include ha B hb in
theorem memLp (v:Process (E:=E) 𝓕 μ h):
    @MemLp _ _ 𝓕.predictable _ _ (fun p=>a p • v p) 2
      ((energyMeasure μ h).trim (predictable_le_product 𝓕)):=by
  apply (Lp.memLp v).of_le_mul (c:=B)
    (ha.smul (Lp.stronglyMeasurable v)).aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun p=>by
    change ‖a p • v p‖≤B*‖v p‖
    rw [norm_smul,Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (hb p) (norm_nonneg _))

/-- Multiplication by an actual bounded predictable scalar field. -/
def mul (v:Process (E:=E) 𝓕 μ h):Process (E:=E) 𝓕 μ h:=
  (memLp 𝓕 μ h a ha B hb v).toLp (fun p=>a p • v p)

theorem ae (v:Process (E:=E) 𝓕 μ h):
    mul 𝓕 μ h a ha B hb v=ᵐ[energyMeasure μ h](fun p=>a p • v p):=
  ae_eq_of_ae_eq_trim (memLp 𝓕 μ h a ha B hb v).coeFn_toLp

theorem sub (v w:Process (E:=E) 𝓕 μ h):
    mul 𝓕 μ h a ha B hb (v-w)=mul 𝓕 μ h a ha B hb v-mul 𝓕 μ h a ha B hb w:=by
  apply Lp.ext
  filter_upwards [(memLp 𝓕 μ h a ha B hb (v-w)).coeFn_toLp,
    (memLp 𝓕 μ h a ha B hb v).coeFn_toLp,(memLp 𝓕 μ h a ha B hb w).coeFn_toLp,
    Lp.coeFn_sub v w,Lp.coeFn_sub (mul 𝓕 μ h a ha B hb v) (mul 𝓕 μ h a ha B hb w)]
    with p huv hv hw hi ho
  change mul 𝓕 μ h a ha B hb (v-w) p=_
  change mul 𝓕 μ h a ha B hb (v-w) p=a p • (v-w) p at huv
  change mul 𝓕 μ h a ha B hb v p=a p • v p at hv
  change mul 𝓕 μ h a ha B hb w p=a p • w p at hw
  rw [huv,ho]
  change a p • (v-w) p=mul 𝓕 μ h a ha B hb v p-mul 𝓕 μ h a ha B hb w p
  rw [hi,hv,hw]
  exact smul_sub _ _ _

theorem add (v w:Process (E:=E) 𝓕 μ h):
    mul 𝓕 μ h a ha B hb (v+w)=mul 𝓕 μ h a ha B hb v+mul 𝓕 μ h a ha B hb w:=by
  apply Lp.ext
  filter_upwards [(memLp 𝓕 μ h a ha B hb (v+w)).coeFn_toLp,
    (memLp 𝓕 μ h a ha B hb v).coeFn_toLp,(memLp 𝓕 μ h a ha B hb w).coeFn_toLp,
    Lp.coeFn_add v w,Lp.coeFn_add (mul 𝓕 μ h a ha B hb v) (mul 𝓕 μ h a ha B hb w)]
    with p huv hv hw hi ho
  change mul 𝓕 μ h a ha B hb (v+w) p=_
  change mul 𝓕 μ h a ha B hb (v+w) p=a p • (v+w) p at huv
  change mul 𝓕 μ h a ha B hb v p=a p • v p at hv
  change mul 𝓕 μ h a ha B hb w p=a p • w p at hw
  rw [huv,ho]
  change a p • (v+w) p=mul 𝓕 μ h a ha B hb v p+mul 𝓕 μ h a ha B hb w p
  rw [hi,hv,hw]
  exact smul_add _ _ _

theorem inverse (b:ℝ≥0×Ω→ℝ)(hbm:StronglyMeasurable[𝓕.predictable] b)
    (C:ℝ)(hbb:∀p,|b p|≤C)(hinv:∀p,b p*a p=1)(v:Process (E:=E) 𝓕 μ h):
    mul 𝓕 μ h b hbm C hbb (mul 𝓕 μ h a ha B hb v)=v:=by
  apply Lp.ext
  filter_upwards [(memLp 𝓕 μ h b hbm C hbb (mul 𝓕 μ h a ha B hb v)).coeFn_toLp,
    (memLp 𝓕 μ h a ha B hb v).coeFn_toLp] with p hout hin
  change mul 𝓕 μ h b hbm C hbb (mul 𝓕 μ h a ha B hb v) p=v p
  change mul 𝓕 μ h b hbm C hbb (mul 𝓕 μ h a ha B hb v) p=b p • mul 𝓕 μ h a ha B hb v p at hout
  change mul 𝓕 μ h a ha B hb v p=a p • v p at hin
  rw [hout,hin,smul_smul,hinv,one_smul]

end SHE.PredictableMultiplier
