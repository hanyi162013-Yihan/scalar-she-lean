module

public import SHE.FiniteCovariancePullback
public import SHE.FirstGammaAffine

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
namespace SHE.FiniteAffineRows
open GaussianIncrement FiniteCovariancePullback
variable {n m : ℕ} {C : Type*} [AddCommGroup C] [Module ℝ C]

theorem mapped_add (L M : State m→L[ℝ]State n) (R : Fin m→C) (i : Fin n) :
    mappedRow (L+M) R i=mappedRow L R i+mappedRow M R i := by
  simp only [mappedRow,coefficient,add_apply,PiLp.add_apply,add_smul,Finset.sum_add_distrib]

theorem mapped_sub (L M : State m→L[ℝ]State n) (R : Fin m→C) (i : Fin n) :
    mappedRow (L-M) R i=mappedRow L R i-mappedRow M R i := by
  simp only [mappedRow,coefficient,sub_apply,PiLp.sub_apply,sub_smul,Finset.sum_sub_distrib]

theorem mapped_smul (a : ℝ) (L : State m→L[ℝ]State n) (R : Fin m→C) (i : Fin n) :
    mappedRow (a • L) R i=a • mappedRow L R i := by
  simp only [mappedRow,coefficient,smul_apply,PiLp.smul_apply,smul_eq_mul,mul_smul,Finset.smul_sum]

theorem mapped_restrict (e : Fin n→Fin m) (R : Fin m→C) (i : Fin n) :
    mappedRow (ObservationBlockMaps.restrict e) R i=R (e i) := by
  simp [mappedRow,coefficient,ObservationBlockMaps.restrict_apply,EuclideanSpace.basisFun_apply,
    PiLp.single_apply,eq_comm]

variable (n : ℕ) (R : Fin ((n+n)+(n+n))→C) (i : Fin n)

theorem mapped_currentU : mappedRow (FirstGammaAffine.currentU n) R i=
    R (Fin.castAdd (n+n) (Fin.castAdd n i)) := by
  have h : FirstGammaAffine.currentU n=ObservationBlockMaps.restrict
      (fun i=>Fin.castAdd (n+n) (Fin.castAdd n i)) := by
    ext z i
    rfl
  rw [h,mapped_restrict]

theorem mapped_currentD : mappedRow (FirstGammaAffine.currentD n) R i=
    R (Fin.castAdd (n+n) (Fin.natAdd n i)) := by
  have h : FirstGammaAffine.currentD n=ObservationBlockMaps.restrict
      (fun i=>Fin.castAdd (n+n) (Fin.natAdd n i)) := by
    ext z i
    rfl
  rw [h,mapped_restrict]

theorem mapped_frozenU : mappedRow (FirstGammaAffine.frozenU n) R i=
    R (Fin.natAdd (n+n) (Fin.castAdd n i)) := by
  have h : FirstGammaAffine.frozenU n=ObservationBlockMaps.restrict
      (fun i=>Fin.natAdd (n+n) (Fin.castAdd n i)) := by
    ext z i
    rfl
  rw [h,mapped_restrict]

theorem mapped_pastD : mappedRow (FirstGammaAffine.pastD n) R i=
    R (Fin.natAdd (n+n) (Fin.natAdd n i)) := by
  have h : FirstGammaAffine.pastD n=ObservationBlockMaps.restrict
      (fun i=>Fin.natAdd (n+n) (Fin.natAdd n i)) := by
    ext z i
    rfl
  rw [h,mapped_restrict]

theorem mapped_terminal_comp (Λ : ℝ) (target : Fin n→ℝ) (L : FirstGammaAffine.Space n→L[ℝ]State n) :
    mappedRow ((FirstGammaAffine.terminalDamping n Λ target).comp L) R i=
      Real.exp (-Λ*target i) • mappedRow L R i := by
  simp only [mappedRow,coefficient,ContinuousLinearMap.comp_apply,FirstGammaAffine.terminalDamping_apply,
    mul_smul,Finset.smul_sum]

theorem mapped_reference (Λ θ : ℝ) (target : Fin n→ℝ) :
    mappedRow (FirstGammaAffine.reference n Λ θ target) R i=
      R (Fin.natAdd (n+n) (Fin.castAdd n i))+
        (θ*Real.exp (-Λ*target i)) • R (Fin.natAdd (n+n) (Fin.natAdd n i)) := by
  rw [FirstGammaAffine.reference,mapped_add,mapped_smul,mapped_terminal_comp,mapped_frozenU,mapped_pastD,smul_smul]

theorem mapped_current (Λ θ t : ℝ) (target : Fin n→ℝ) :
    mappedRow (FirstGammaAffine.current n Λ θ target t) R i=
      R (Fin.castAdd (n+n) (Fin.castAdd n i))+
        ClippedExponential.coefficient Λ θ t • R (Fin.castAdd (n+n) (Fin.natAdd n i))+
        (θ*Real.exp (-Λ*target i)-ClippedExponential.coefficient Λ θ t) •
          R (Fin.natAdd (n+n) (Fin.natAdd n i)) := by
  rw [FirstGammaAffine.current,DampedAffineGaussian.linear,mapped_add,mapped_smul,
    FirstGammaAffine.baseCurrent,mapped_add,mapped_smul,mapped_terminal_comp,
    FirstGammaAffine.dynamic,mapped_sub,mapped_currentU,mapped_currentD,mapped_pastD]
  module

end SHE.FiniteAffineRows
