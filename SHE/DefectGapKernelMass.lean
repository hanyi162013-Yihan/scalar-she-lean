module
public import SHE.DefectGapOffsets
public import SHE.FiniteKernelMixture
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
namespace SHE.DefectGapKernelMass
open Set MeasureTheory Real
open scoped NNReal ENNReal BigOperators

def offsets (k:ℕ)(d:Fin k→ℝ):Fin (1+k)→ℝ:=
  DefectGapOffsets.offsets k (fun i=>max 0 (d i))

def realKernel (Λ ρ:ℝ)(k:ℕ)(d:Fin k→ℝ)(τ:ℝ):ℝ:=
  ∑i:Fin (1+k),∑j:Fin (1+k),DefectCombinedTime.kernel Λ ρ (offsets k d i) (offsets k d j) τ

def kernel (Λ ρ:ℝ)(k:ℕ)(p:(Fin k→ℝ)×ℝ):ℝ≥0∞:=ENNReal.ofReal (realKernel Λ ρ k p.1 p.2)
def cost (Λ ρ h:ℝ)(k:ℕ):ℝ:=((1+k:ℕ):ℝ)^2*(4+2/ρ+log (2+Λ*h))

theorem offsets_nonneg (k:ℕ)(d:Fin k→ℝ):∀i,0≤offsets k d i:=
  DefectGapOffsets.offsets_nonneg k _ (fun i=>le_max_left _ _)

theorem offsets_eq (k:ℕ)(d:Fin k→ℝ)(hd:∀i,0≤d i):offsets k d=DefectGapOffsets.offsets k d:=by
  have he:(fun i=>max 0 (d i))=d:=funext (fun i=>max_eq_right (hd i))
  rw [offsets,he]

theorem measurable (Λ ρ:ℝ)(k:ℕ):Measurable (kernel Λ ρ k):=by
  have ho:Measurable (offsets k):=(DefectGapOffsets.offsets_measurable k).comp
    (Measurable.of_eval (fun i=>measurable_const.max (measurable_pi_apply i)))
  have hi(i:Fin (1+k)):Measurable (fun p:(Fin k→ℝ)×ℝ=>offsets k p.1 i):=
    ((measurable_pi_apply i).comp ho).comp measurable_fst
  unfold kernel realKernel
  apply ENNReal.measurable_ofReal.comp
  apply Finset.measurable_sum
  intro i _
  apply Finset.measurable_sum
  intro j _
  unfold DefectCombinedTime.kernel SHE.newTimeKernel
  fun_prop

/-- Full original-pair new-time mass, uniform over every relative old
history. The same finite pair sum is retained, with no partition choice. -/
theorem mass {Λ ρ h:ℝ}(hΛ:0<Λ)(hρ:0<ρ)(hρ1:ρ≤1)(hh:0≤h)(k:ℕ)(d:Fin k→ℝ):
    (∫⁻τ,kernel Λ ρ k (d,τ) ∂volume.restrict (Ioc (0:ℝ) h))≤ENNReal.ofReal (cost Λ ρ h k):=by
  have hp(i j:Fin (1+k)):=DefectCombinedTime.integral hΛ hρ hρ1
    (offsets_nonneg k d i) (offsets_nonneg k d j) hh le_rfl
  have hi(i j:Fin (1+k)):IntegrableOn
      (DefectCombinedTime.kernel Λ ρ (offsets k d i) (offsets k d j)) (Ioc 0 h):=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hh).mp (hp i j).1
  have hs:IntegrableOn (realKernel Λ ρ k d) (Ioc 0 h):=
    integrable_finset_sum _ (fun i _=>integrable_finset_sum _ (fun j _=>hi i j))
  have hn:∀ᵐτ:ℝ∂volume.restrict (Ioc (0:ℝ) h),0≤realKernel Λ ρ k d τ:=by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with τ hτ
    exact Finset.sum_nonneg (fun i _=>Finset.sum_nonneg (fun j _=>
      DefectCombinedTime.nonneg hΛ.le (offsets_nonneg k d i) (offsets_nonneg k d j) hτ.1.le))
  change (∫⁻τ,ENNReal.ofReal (realKernel Λ ρ k d τ) ∂volume.restrict (Ioc (0:ℝ) h))≤_
  rw [←ofReal_integral_eq_lintegral_ofReal hs hn]
  apply ENNReal.ofReal_le_ofReal
  unfold realKernel cost
  rw [integral_finsetSum _ (fun i _=>integrable_finset_sum _ (fun j _=>hi i j))]
  simp_rw [integral_finsetSum _ (fun j _=>hi _ j)]
  calc
    _≤∑i:Fin (1+k),∑j:Fin (1+k),(4+2/ρ+log (2+Λ*h)):=by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      rw [←intervalIntegral.integral_of_le hh]
      exact (hp i j).2
    _=_:=by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul];ring

end SHE.DefectGapKernelMass
