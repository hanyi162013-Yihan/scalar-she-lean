module

public import SHE.UniformSmooth
public import Mathlib.MeasureTheory.Constructions.Pi

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 750000
noncomputable section
namespace SHE.RootSmoothSums
open Set MeasureTheory SmoothCylinders UniformSmooth
open scoped BigOperators
variable {X E G : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

theorem uniform_add {F H : X→E→G} (hF : UniformBoundedSmooth F) (hH : UniformBoundedSmooth H) :
    UniformBoundedSmooth (fun x z=>F x z+H x z) := by
  refine ⟨fun x=>(hF.smooth x).add (hH.smooth x),fun k=>?_⟩
  obtain ⟨M,hM0,hM⟩:=hF.bounds k
  obtain ⟨N,hN0,hN⟩:=hH.bounds k
  refine ⟨M+N,add_nonneg hM0 hN0,fun x z=>?_⟩
  change ‖iteratedFDeriv ℝ k (F x+H x) z‖≤M+N
  rw [iteratedFDeriv_add_apply (i:=k) (x:=z) ((hF.smooth x).of_le (by simp)).contDiffAt
    ((hH.smooth x).of_le (by simp)).contDiffAt]
  exact (norm_add_le _ _).trans (add_le_add (hM x z) (hN x z))

def rootSum (F : ℕ→X→E→G) (s : Finset ℕ) (x : X) (z : E) : G:=∑ j∈s,F j x z

theorem rootSum_uniform (F : ℕ→X→E→G) (hF : ∀ j,UniformBoundedSmooth (F j)) (s : Finset ℕ) :
    UniformBoundedSmooth (rootSum F s) := by
  unfold rootSum
  induction s using Finset.induction_on with
  | empty=>
    simpa only [rootSum,Finset.sum_empty] using
      (UniformBoundedSmooth.parameter_const (P:=X) (E:=E) (fun _=>(0:G)) (le_refl (0:ℝ)) (fun _=>by simp))
  | @insert j s hj ih=>
    simpa only [rootSum,Finset.sum_insert hj] using uniform_add (hF j) ih

theorem rootSum_measurable [MeasurableSpace X] [MeasurableSpace G] [BorelSpace G]
    [SecondCountableTopology G] [MeasurableSpace E]
    (F : ℕ→X→E→G) (hF : ∀ j,Measurable (fun z : X×E=>F j z.1 z.2)) (s : Finset ℕ) :
    Measurable (fun z : X×E=>rootSum F s z.1 z.2):=
  Finset.measurable_sum s (fun j _=>hF j)
end SHE.RootSmoothSums
