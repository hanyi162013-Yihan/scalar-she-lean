module

public import SHEStochastic.MatrixGlobalHaarGram
public import SHEStochastic.DyadicVectorStep

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
noncomputable section

namespace SHEStochastic.MatrixGlobalHaarComplete
open MeasureTheory Matrix SHE SHE.FiniteHaar
open scoped MatrixOrder Matrix.Norms.L2Operator Topology

local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
variable {d : Type*} [Fintype d] [DecidableEq d]
local notation "μ" => AddCircle.haarAddCircle (T := (1 : ℝ))

def finiteColumn (n : ℕ) (κ : AddCircle (1 : ℝ) → Matrix d d ℝ)
    (k : d × Option (DetailIndex n)) : DyadicVectorStep.Physical (d := d) :=
  DyadicVectorStep.step n (fun z => MatrixHaarRootColumns.column
    (MatrixFiniteHaar.haarColumn n (MatrixDyadicMass.profile κ n) k.2 z) k.1)

theorem finiteColumn_eq (n : ℕ) (κ : AddCircle (1 : ℝ) → Matrix d d ℝ)
    (hκ : Integrable κ μ) (k : d × Option (DetailIndex n)) :
    finiteColumn n κ k=MatrixGlobalHaar.column κ (modePath n k.2) k.1 := by
  apply Lp.ext
  have hm : nodeMode n (modePath n k.2) (modePath_depth n k.2)=k.2 := by
    apply modePath_injective n
    exact modePath_nodeMode _ _ _
  filter_upwards [DyadicVectorStep.step_ae n (fun z => MatrixHaarRootColumns.column
      (MatrixFiniteHaar.haarColumn n (MatrixDyadicMass.profile κ n) k.2 z) k.1),
    MatrixDyadicCoherence.column_ae κ (modePath n k.2) k.1,
    MatrixDyadicCoherence.coefficient_grid κ hκ n (modePath n k.2) (modePath_depth n k.2)] with x hs hg hc
  change DyadicVectorStep.step n _ x=_
  rw [hs, hg, hc, hm]
  rfl

/-- Finite matrix invertibility expands every literal vector dyadic
step in the actual countable covariance-adapted columns. -/
theorem step_mem_span (n : ℕ) (κ : AddCircle (1 : ℝ) → Matrix d d ℝ)
    (hκ : Integrable κ μ) (hp : ∀ z, (MatrixDyadicMass.profile κ n z).PosDef)
    (a : Grid n → EuclideanSpace ℝ d) :
    DyadicVectorStep.step n a∈Submodule.span ℝ
      (Set.range (fun k : d × HaarNode => MatrixGlobalHaar.column κ k.2 k.1)) := by
  let H := MatrixFiniteFactor.haarMatrix n (MatrixDyadicMass.profile κ n)
  let L := MatrixFiniteFactor.localFactor n (MatrixDyadicMass.profile κ n)
  have hInv : H*Lᴴ=1 := by
    have hh := congrArg Matrix.conjTranspose (MatrixFiniteFactor.right_inverse n _ hp)
    simpa only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      Matrix.conjTranspose_one] using hh
  let v : d × Grid n → ℝ := fun x => a x.2 x.1
  let z := Lᴴ*ᵥv
  have hz : H*ᵥz=v := by
    change H*ᵥ(Lᴴ*ᵥv)=v
    rw [Matrix.mulVec_mulVec, hInv, Matrix.one_mulVec]
  have hEq : DyadicVectorStep.step n a=∑ k : d × Option (DetailIndex n), z k • finiteColumn n κ k := by
    apply Lp.ext
    have hs : ∀ᵐ x ∂μ, ∀ k : d × Option (DetailIndex n), finiteColumn n κ k x=
        MatrixHaarRootColumns.column (MatrixFiniteHaar.haarColumn n (MatrixDyadicMass.profile κ n)
          k.2 (MatrixDyadicPairing.leaf n x)) k.1 :=
      ae_all_iff.mpr (fun k => DyadicVectorStep.step_ae n _)
    have hsm : ∀ᵐ x ∂μ, ∀ k : d × Option (DetailIndex n),
        (z k • finiteColumn n κ k) x=z k • finiteColumn n κ k x :=
      ae_all_iff.mpr (fun k => Lp.coeFn_smul (z k) (finiteColumn n κ k))
    filter_upwards [DyadicVectorStep.step_ae n a,
      Lp.coeFn_finsetSum Finset.univ (fun k : d × Option (DetailIndex n) => z k • finiteColumn n κ k),
      hs, hsm] with x ha hsum hs hsm
    rw [ha, hsum]
    ext i
    have he := congrFun hz (i, MatrixDyadicPairing.leaf n x)
    simp only [Matrix.mulVec, dotProduct, H, MatrixFiniteFactor.haarMatrix, v] at he
    simp only [Finset.sum_apply, hsm, hs, PiLp.smul_apply, smul_eq_mul,
      MatrixHaarRootColumns.column_apply]
    rw [show (∑ k : d × Option (DetailIndex n), z k • MatrixHaarRootColumns.column
        (MatrixFiniteHaar.haarColumn n (MatrixDyadicMass.profile κ n) k.2 (MatrixDyadicPairing.leaf n x))
        k.1).ofLp i=
        ∑ k : d × Option (DetailIndex n), z k *
          MatrixFiniteHaar.haarColumn n (MatrixDyadicMass.profile κ n) k.2 (MatrixDyadicPairing.leaf n x) i k.1 from by
      simp only [WithLp.ofLp_sum, Finset.sum_apply, PiLp.smul_apply, smul_eq_mul,
        MatrixHaarRootColumns.column_apply]]
    simpa only [mul_comm] using he.symm
  rw [hEq]
  apply Submodule.sum_mem
  intro k hk
  apply Submodule.smul_mem
  rw [finiteColumn_eq n κ hκ]
  exact Submodule.subset_span ⟨(k.1, modePath n k.2), rfl⟩

/-- Completeness in the actual vector spatial `L²` space follows from
finite Haar invertibility and the reused scalar dyadic density theorem. -/
theorem dense (κ : AddCircle (1 : ℝ) → Matrix d d ℝ) (hκ : Integrable κ μ)
    (m : ℝ) (hm : 0 < m) (hLo : ∀ᵐ x ∂μ, m • (1 : Matrix d d ℝ) ≤ κ x) :
    (Submodule.span ℝ (Set.range
      (fun k : d × HaarNode => MatrixGlobalHaar.column κ k.2 k.1))).topologicalClosure=⊤ := by
  apply top_unique
  intro u hu
  apply Submodule.isClosed_topologicalClosure _ |>.mem_of_tendsto (DyadicVectorStep.tendsto u)
  exact Filter.Eventually.of_forall (fun n => Submodule.le_topologicalClosure _
    (step_mem_span n κ hκ (MatrixDyadicMass.positive κ hκ m hm hLo n) _))

end SHEStochastic.MatrixGlobalHaarComplete
