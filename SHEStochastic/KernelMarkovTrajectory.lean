module

public import Mathlib.Probability.Kernel.IonescuTulcea.Traj
public import Mathlib.Probability.Kernel.Composition.Lemmas
public import Mathlib.Probability.Kernel.Composition.IntegralCompProd

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 700000
noncomputable section

namespace SHEStochastic.KernelMarkovTrajectory
open MeasureTheory ProbabilityTheory
open scoped ENNReal
variable {X : Type*} [MeasurableSpace X]

def last (n : ℕ) (p : (i : Finset.Iic n) → X) : X := p ⟨n,Finset.mem_Iic.mpr le_rfl⟩

theorem last_measurable (n : ℕ) : Measurable (last (X := X) n) := measurable_pi_apply _

def transition (K : ℕ → Kernel X X) (n : ℕ) : Kernel ((i : Finset.Iic n) → X) X :=
  (K n).comap (last n) (last_measurable n)

instance (K : ℕ → Kernel X X) [∀ n,IsMarkovKernel (K n)] (n : ℕ) :
    IsMarkovKernel (transition K n) := inferInstanceAs (IsMarkovKernel ((K n).comap _ _))

/-- An infinite chain of actual Borel continuation kernels, supplied
directly by mathlib's Ionescu--Tulcea construction. -/
def law (μ₀ : Measure X) (K : ℕ → Kernel X X) [∀ n,IsMarkovKernel (K n)] : Measure (ℕ → X) :=
  Kernel.trajMeasure (X := fun _ : ℕ => X) μ₀ (transition K)

instance (μ₀ : Measure X) [IsProbabilityMeasure μ₀] (K : ℕ → Kernel X X) [∀ n,IsMarkovKernel (K n)] :
    IsProbabilityMeasure (law μ₀ K) := inferInstanceAs (IsProbabilityMeasure (Kernel.trajMeasure (X := fun _ : ℕ => X) μ₀ (transition K)))

theorem marginal_next (μ₀ : Measure X) [IsProbabilityMeasure μ₀]
    (K : ℕ → Kernel X X) [∀ n,IsMarkovKernel (K n)] (n : ℕ) :
    (law μ₀ K).map (fun p => p (n+1))=(K n) ∘ₘ ((law μ₀ K).map (fun p => p n)) := by
  let ν := law μ₀ K
  have hPrefix := Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure
    (X := fun _ : ℕ => X) (μ₀ := μ₀) (κ := transition K) (a := n)
  have h := congrArg (fun η : Measure (((i : Finset.Iic n) → X)×X) => η.map Prod.snd) hPrefix
  change (((ν.map (Preorder.frestrictLe n)) ⊗ₘ transition K n).snd)=
    (ν.map (fun p => (Preorder.frestrictLe n p,p (n+1)))).map Prod.snd at h
  rw [Measure.snd_compProd,Measure.map_map measurable_snd (by fun_prop)] at h
  have hComp : (K n) ∘ₘ (ν.map (fun p => p n))=
      (transition K n) ∘ₘ (ν.map (Preorder.frestrictLe n)) := by
    have he : (fun p : ℕ → X => p n)=last n ∘ Preorder.frestrictLe n := rfl
    rw [he,←Measure.map_map (last_measurable n) (by fun_prop)]
    exact Measure.bind_map (last_measurable n).aemeasurable (K n).aemeasurable
  exact h.symm.trans hComp.symm

theorem marginal_zero (μ₀ : Measure X) [IsProbabilityMeasure μ₀]
    (K : ℕ → Kernel X X) [∀ n,IsMarkovKernel (K n)] :
    (law μ₀ K).map (fun p => p 0)=μ₀ := by
  have hm : (Kernel.traj (X := fun _ : ℕ => X) (transition K) 0).map (fun p => p 0)=
      Kernel.deterministic (last (X := X) 0) (last_measurable 0) := by
    have he : (fun p : ℕ → X => p 0)=last 0 ∘ Preorder.frestrictLe 0 := rfl
    rw [he,Kernel.map_comp_right _ (by fun_prop) (last_measurable 0),
      Kernel.traj_map_frestrictLe,Kernel.partialTraj_self,Kernel.id_map]
  rw [law,Kernel.trajMeasure,Measure.map_comp _ _ (by fun_prop),hm,
    Measure.deterministic_comp_eq_map,Measure.map_map (last_measurable 0) (by fun_prop)]
  have he : last 0 ∘ (MeasurableEquiv.piUnique (fun _ : Finset.Iic 0 => X)).symm=id := by
    funext x
    rfl
  rw [he,Measure.map_id]

/-- Prescribed successive marginal laws identify every actual block
of the infinite chain, including laws selected separately at each step. -/
theorem marginals (μ₀ : Measure X) [IsProbabilityMeasure μ₀]
    (K : ℕ → Kernel X X) [∀ n,IsMarkovKernel (K n)] (Q : ℕ → Measure X)
    (h₀ : Q 0=μ₀) (hStep : ∀ n,(K n) ∘ₘ Q n=Q (n+1)) :
    ∀ n,(law μ₀ K).map (fun p => p n)=Q n := by
  intro n
  induction n with
  | zero => exact (marginal_zero μ₀ K).trans h₀.symm
  | succ n ih => rw [marginal_next,ih,hStep]

/-- A measurable relation supported by each continuation kernel holds
for adjacent coordinates of the actual infinite trajectory. -/
theorem ae_step (μ₀ : Measure X) [IsProbabilityMeasure μ₀]
    (K : ℕ → Kernel X X) [∀ n,IsMarkovKernel (K n)] (n : ℕ)
    (R : X → X → Prop) (hR : MeasurableSet {p : X×X | R p.1 p.2})
    (h : ∀ᵐ x ∂(law μ₀ K).map (fun p => p n),∀ᵐ y ∂K n x,R x y) :
    ∀ᵐ p ∂law μ₀ K,R (p n) (p (n+1)) := by
  let ν := law μ₀ K
  have hLast : (ν.map (Preorder.frestrictLe n)).map (last n)=ν.map (fun p => p n) := by
    rw [Measure.map_map (last_measurable n) (by fun_prop)]
    rfl
  have hPre : ∀ᵐ p ∂ν.map (Preorder.frestrictLe n),∀ᵐ y ∂K n (last n p),R (last n p) y := by
    apply ae_of_ae_map (μ := ν.map (Preorder.frestrictLe n))
      (p := fun x => ∀ᵐ y ∂K n x,R x y) (last_measurable n).aemeasurable
    rw [hLast]
    exact h
  have hJoint : ∀ᵐ p ∂(ν.map (Preorder.frestrictLe n)) ⊗ₘ transition K n,R (last n p.1) p.2 :=
    Measure.ae_compProd_of_ae_ae
      (hR.preimage (((last_measurable n).comp measurable_fst).prodMk measurable_snd)) hPre
  have he := Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure
    (X := fun _ : ℕ => X) (μ₀ := μ₀) (κ := transition K) (a := n)
  change (ν.map (Preorder.frestrictLe n)) ⊗ₘ transition K n=
    ν.map (fun p => (Preorder.frestrictLe n p,p (n+1))) at he
  rw [he] at hJoint
  exact ae_of_ae_map (μ := ν)
    (f := fun p : ℕ → X => (Preorder.frestrictLe n p,p (n+1)))
    (p := fun z : ((i : Finset.Iic n) → X)×X => R (last n z.1) z.2)
    (by fun_prop) hJoint

/-- The full prefix is retained in continuation expectations. This is
stronger than knowledge of the one-block marginal distributions. -/
theorem integral_step {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (μ₀ : Measure X) [IsProbabilityMeasure μ₀]
    (K : ℕ → Kernel X X) [∀ n,IsMarkovKernel (K n)] (n : ℕ)
    (f : (((i : Finset.Iic n) → X)×X) → E)
    (hf : Integrable f (((law μ₀ K).map (Preorder.frestrictLe n)) ⊗ₘ transition K n)) :
    (∫ p,f (Preorder.frestrictLe n p,p (n+1)) ∂law μ₀ K)=
      ∫ x,∫ y,f (x,y) ∂K n (last n x) ∂(law μ₀ K).map (Preorder.frestrictLe n) := by
  have he := Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure
    (X := fun _ : ℕ => X) (μ₀ := μ₀) (κ := transition K) (a := n)
  change ((law μ₀ K).map (Preorder.frestrictLe n)) ⊗ₘ transition K n=
    (law μ₀ K).map (fun p => (Preorder.frestrictLe n p,p (n+1))) at he
  calc
    _ = ∫ z,f z ∂((law μ₀ K).map (fun p => (Preorder.frestrictLe n p,p (n+1)))) :=
      (integral_map (by fun_prop) (he ▸ hf.aestronglyMeasurable)).symm
    _ = ∫ z,f z ∂(((law μ₀ K).map (Preorder.frestrictLe n)) ⊗ₘ transition K n) := by rw [←he]
    _ = _ := Measure.integral_compProd hf

end SHEStochastic.KernelMarkovTrajectory
