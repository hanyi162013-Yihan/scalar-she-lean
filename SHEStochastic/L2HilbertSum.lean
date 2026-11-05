module

public import SHE.LpEnergy
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.l2Space

/-! General L² facts used to lift scalar stochastic integrals to Hilbert spaces. -/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHEStochastic.L2HilbertSum
open MeasureTheory
open scoped ENNReal

variable {Ω E F : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
  [NormedAddCommGroup E] [NormedAddCommGroup F]

section Basic
variable [NormedSpace ℝ E] [NormedSpace ℝ F]

/-- Existing pointwise Lp composition preserves an isometry exactly. -/
def lift (V : E →ₗᵢ[ℝ] F) : Lp E 2 μ →ₗᵢ[ℝ] Lp F 2 μ where
  toLinearMap := (V.toContinuousLinearMap.compLpL 2 μ).toLinearMap
  norm_map' f := by
    rw [Lp.norm_def, Lp.norm_def]
    congr 1
    apply eLpNorm_congr_norm_ae (Lp.aestronglyMeasurable _) (Lp.aestronglyMeasurable _)
    filter_upwards [V.toContinuousLinearMap.coeFn_compLpL f] with ω hω
    exact (congrArg norm hω).trans (V.norm_map _)

theorem lift_ae (V : E →ₗᵢ[ℝ] F) (f : Lp E 2 μ) :
    lift μ V f =ᵐ[μ] fun ω => V (f ω) :=
  V.toContinuousLinearMap.coeFn_compLpL f

end Basic

section Orthogonal
variable {ι : Type*} {G : ι → Type*}
  [∀ i, NormedAddCommGroup (G i)] [∀ i, InnerProductSpace ℝ (G i)]
  [InnerProductSpace ℝ F] (V : ∀ i, G i →ₗᵢ[ℝ] F)

theorem orthogonal (hV : OrthogonalFamily ℝ G V) :
    OrthogonalFamily ℝ (fun i => Lp (G i) 2 μ) (fun i => lift μ (V i)) := by
  intro i j hij f g
  rw [L2.inner_def]
  apply integral_eq_zero_of_ae
  filter_upwards [lift_ae μ (V i) f, lift_ae μ (V j) g] with ω hf hg
  rw [hf, hg]
  exact hV hij (f ω) (g ω)

variable [CompleteSpace F]

/-- The Hilbert-sum construction is supplied by mathlib; only its L²
orthogonality check is needed here. -/
def sumIsometry (hV : OrthogonalFamily ℝ G V) :
    lp (fun i => Lp (G i) 2 μ) 2 →ₗᵢ[ℝ] Lp F 2 μ :=
  (orthogonal μ V hV).linearIsometry

variable [∀ i, CompleteSpace (G i)]

theorem coordinate (hV : IsHilbertSum ℝ G V) (x : F) (i : ι) :
    hV.linearIsometryEquiv x i = (V i).toContinuousLinearMap.adjoint x := by
  classical
  apply ext_inner_left ℝ
  intro a
  calc
    _ = inner ℝ (lp.single 2 i a) (hV.linearIsometryEquiv x) :=
      (lp.inner_single_left i a _).symm
    _ = inner ℝ (hV.linearIsometryEquiv.symm (lp.single 2 i a)) x := by
      rw [← hV.linearIsometryEquiv.symm.inner_map_map, LinearIsometryEquiv.symm_apply_apply]
    _ = inner ℝ (V i a) x := by rw [hV.linearIsometryEquiv_symm_apply_single]
    _ = _ := ((V i).toContinuousLinearMap.adjoint_inner_right _ _).symm

theorem inner_lift (i : ι) (f : Lp (G i) 2 μ) (g : Lp F 2 μ) :
    inner ℝ (lift μ (V i) f) g =
      inner ℝ f (((V i).toContinuousLinearMap.adjoint.compLpL 2 μ) g) := by
  rw [L2.inner_def, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [lift_ae μ (V i) f,
    (V i).toContinuousLinearMap.adjoint.coeFn_compLpL g] with ω hf hg
  rw [hf, hg]
  exact ((V i).toContinuousLinearMap.adjoint_inner_right _ _).symm

theorem lift_adjoint (i : ι) :
    (lift μ (V i)).toContinuousLinearMap.adjoint =
      (V i).toContinuousLinearMap.adjoint.compLpL 2 μ := by
  ext1 g
  apply ext_inner_left ℝ
  intro f
  exact ((lift μ (V i)).toContinuousLinearMap.adjoint_inner_right _ _).trans
    (inner_lift μ V i f g)

/-- A countable orthogonal Hilbert decomposition remains total after
passing to L². No separability assumption on the probability space is used. -/
theorem total [Countable ι] (hV : IsHilbertSum ℝ G V) :
    IsHilbertSum ℝ (fun i => Lp (G i) 2 μ) (fun i => lift μ (V i)) := by
  let S : Submodule ℝ (Lp F 2 μ) :=
    ⨆ i, LinearMap.range (lift μ (V i)).toLinearMap
  have hbot : Sᗮ = ⊥ := by
    apply le_antisymm
    · intro y hy
      change y = 0
      have hc (i : ι) : ((V i).toContinuousLinearMap.adjoint.compLpL 2 μ) y = 0 := by
        let f := ((V i).toContinuousLinearMap.adjoint.compLpL 2 μ) y
        have hz : inner ℝ (lift μ (V i) f) y = 0 :=
          (Submodule.mem_orthogonal _ _).mp hy _
            (Submodule.mem_iSup_of_mem i (LinearMap.mem_range_self _ f))
        rw [inner_lift] at hz
        exact inner_self_eq_zero.mp hz
      have hcae (i : ι) : ∀ᵐ ω ∂μ, (V i).toContinuousLinearMap.adjoint (y ω) = 0 := by
        have hzero : (((V i).toContinuousLinearMap.adjoint.compLpL 2 μ) y : Ω → G i)
            =ᵐ[μ] fun _ => 0 := by
          rw [hc i]
          exact Lp.coeFn_zero _ _ _
        exact ((V i).toContinuousLinearMap.adjoint.coeFn_compLpL y).symm.trans hzero
      apply Lp.ext
      filter_upwards [ae_all_iff.mpr hcae, Lp.coeFn_zero F 2 μ]
        with ω hω hzero
      rw [hzero]
      obtain ⟨a, ha⟩ := hV.surjective_isometry (y ω)
      have hs := (innerSL ℝ (y ω)).hasSum
        (hV.OrthogonalFamily.hasSum_linearIsometry a)
      have hi (i : ι) : inner ℝ (y ω) (V i (a i)) = 0 := by
        calc
          _ = inner ℝ (a i) ((V i).toContinuousLinearMap.adjoint (y ω)) :=
            (real_inner_comm _ _).trans
              ((V i).toContinuousLinearMap.adjoint_inner_right _ _).symm
          _ = 0 := by rw [hω i]; simp
      have hz : inner ℝ (y ω) (y ω) = 0 := by
        rw [ha] at hs
        exact hs.unique (by simpa only [innerSL_apply_apply, hi] using
          (hasSum_zero : HasSum (fun _ : ι => (0 : ℝ)) 0))
      exact inner_self_eq_zero.mp hz
    · exact bot_le
  apply IsHilbertSum.mk (orthogonal μ V hV.OrthogonalFamily)
  exact (Submodule.topologicalClosure_eq_top_iff.mpr hbot).ge

end Orthogonal
end SHEStochastic.L2HilbertSum
