module

public import SHEStochastic.MatrixSylvesterSmooth
public import SHEStochastic.MatrixHaarPositive
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1100000
noncomputable section

namespace SHEStochastic.MatrixSqrtSmooth
open Matrix Filter
open scoped MatrixOrder Matrix.Norms.L2Operator Topology

variable {d : Type*} [Fintype d] [DecidableEq d]

/-- The actual positive CFC square root is smooth in the positive cone
near a positive definite matrix. The smooth extension is constructed by
the inverse function theorem applied to matrix squaring. -/
theorem within (A : Matrix d d ℝ) (hA : A.PosDef) :
    ContDiffWithinAt ℝ ⊤ CFC.sqrt {B : Matrix d d ℝ | 0≤B} A := by
  let S := CFC.sqrt A
  have hS : S.PosDef := MatrixHaarPositive.sqrt_posDef A hA
  have hsq : S*S=A := CFC.sqrt_mul_sqrt_self A hA.posSemidef.nonneg
  obtain ⟨f,hf,hfA,hinv⟩ := MatrixSylvesterSmooth.smooth_local_inverse S hS
  rw [hsq] at hf hfA
  have hc : ContinuousWithinAt (CFC.sqrt : Matrix d d ℝ → Matrix d d ℝ) {B | 0≤B} A :=
    CFC.continuousOn_sqrt A hA.posSemidef.nonneg
  have he : CFC.sqrt =ᶠ[𝓝[{B : Matrix d d ℝ | 0≤B}] A] f := by
    filter_upwards [hc hinv, self_mem_nhdsWithin] with B hB hpos
    change f (CFC.sqrt B*CFC.sqrt B)=CFC.sqrt B at hB
    rw [CFC.sqrt_mul_sqrt_self B hpos] at hB
    exact hB.symm
  exact hf.contDiffWithinAt.congr_of_eventuallyEq he hfA.symm

/-- Smooth positive-matrix parameterizations can use the existing CFC
square root directly; there is no auxiliary derivative assumption. -/
theorem comp {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {g : E → Matrix d d ℝ} {x : E} {k : WithTop ℕ∞}
    (hg : ContDiffAt ℝ k g x) (hpos : (g x).PosDef)
    (hcone : ∀ᶠ y in 𝓝 x, 0≤g y) :
    ContDiffAt ℝ k (fun y ↦ CFC.sqrt (g y)) x := by
  have hs : ContDiffWithinAt ℝ k CFC.sqrt {B : Matrix d d ℝ | 0≤B} (g x) :=
    (within (g x) hpos).of_le le_top
  have hh := hs.comp_of_preimage_mem_nhdsWithin x (hg.contDiffWithinAt (s := Set.univ))
    (by
      change {y | 0≤g y} ∈ 𝓝[Set.univ] x
      rw [nhdsWithin_univ]
      exact hcone)
  simpa only [Function.comp_def, contDiffWithinAt_univ] using hh

end SHEStochastic.MatrixSqrtSmooth
